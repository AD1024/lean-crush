import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Theories
import Crush.Translation.HOEncoding
open Lean Meta

/-!
# The translation driver: `Expr → SMT.Term`

Lowers a (monomorphic, first-order-after-encoding) Lean `Expr` into an
`SMT.Term`, dispatching to user `@[crush_translate]` handlers before the default
structural translator. This is the piece that constructs the `TranslationCtx`
closures (`emitTerm`/`emitSort`/`declare`) handlers recurse through.

Covers propositional/Boolean structure, equality, quantifiers, `Int`/`Nat` (Nat via
Int with a `≥ 0` guard), bit-vectors, strings, datatypes, and the higher-order
encoding. Anything unrecognized becomes a fresh uninterpreted symbol, so
translation degrades rather than crashing.

## Why the definitions in this file are `partial`

Elsewhere in the codebase `partial` has been eliminated in favour of real
termination proofs, because a `partial` def is defined via `Inhabited` rather than by
recursion: it has no unfold equations and is opaque to `decide`/`simp`/`rfl`, so
nothing can be proven about it.

Here it is unavoidable, and for a specific reason worth stating precisely. These
functions recurse on a Lean `Expr` while calling `whnf`, and **the recursion depth is
not bounded by the input term**. Given

```lean
def Grow : Nat → Type
  | 0 => Int
  | n+1 => Grow n × Grow n
```

the input `Grow 12` is a three-node `Expr`, but `emitSort` must traverse its unfolded
form: 4096 leaves. No measure on `sizeOf e` can dominate that, since the work is
driven by *definitional unfolding* rather than by the syntax of the argument. In
general `whnf` on a user-supplied definition need not terminate at all; Lean bounds
it with `maxRecDepth` rather than a proof.

This is the same reason Lean's own elaborator and tactic framework are written with
`partial`: these are metaprograms that *construct* SMT terms. Soundness of a closed
goal comes from the discharge policy (`crush.trust`) — under `reconstruct` the verdict
is replayed into a kernel-checked Lean proof from the unsat core, so the translator and
solver are only search heuristics — not from reasoning about the translator itself.
-/

namespace Crush

open SMT

/-- A legal, non-panicking symbol hint from a Lean name (last component, or a
fallback for anonymous/numeric names). `Name.getString!` panics on those. -/
def nameHint : Name → String
  | .str _ s => s
  | .num p _ => nameHint p
  | .anonymous => "f"

/-- The natural-number value of an `@OfNat.ofNat _ (n : Nat lit) _`, if literal.
The numeral argument is a raw `Expr.lit (.natVal _)`, so we read it directly. -/
def getNatLit? (e : Expr) : TranslateM (Option Nat) := do
  match_expr e with
  | OfNat.ofNat _ n _ =>
    match (← whnf n) with
    | .lit (.natVal k) => return some k
    | _ => return none
  | _ => return none

/-- Track which sorts have had their `declare-sort` emitted, reusing the name map
with a sentinel key so we don't re-declare. -/
def declaredSort (name : String) : TranslateM Bool := do
  return (← get).atomToName.contains s!"__sortdecl__{name}"

def markSortDeclared (name : String) : TranslateM Unit :=
  modify fun s => { s with atomToName := s.atomToName.insert s!"__sortdecl__{name}" name }

/-- Whether a function symbol has been declared. -/
def declaredFun (name : String) : TranslateM Bool := do
  return (← get).atomToName.contains s!"__fundecl__{name}"

def markFunDeclared (name : String) : TranslateM Unit :=
  modify fun s => { s with atomToName := s.atomToName.insert s!"__fundecl__{name}" name }

/-- Head-and-args view that treats a bare constant/fvar as a nullary application. -/
def getAppFnArgs' (e : Expr) : Expr × Array Expr :=
  (e.getAppFn, e.getAppArgs)

/-- Whether `e`'s Lean type is `Nat` (so it is encoded as a non-negative `Int`). -/
def isNatTyped (e : Expr) : TranslateM Bool := do
  return (← whnf (← inferType e)).isConstOf ``Nat

/-- Whether the instance argument at position `i` of the application `e` is the one
instance synthesis would pick.

Recognizing `HAdd.hAdd _ _ _ inst a b` as SMT `+` assumes `inst` is the *standard*
instance. A user can supply another — `⟨fun _ _ => 99⟩` is a legal `HAdd Int Int Int`
— and then `1 + 2` is `99`, not `3`. Matching on the head alone therefore imports
arithmetic that does not hold, and lets the solver prove false goals.

Returns `false` when synthesis fails, so an exotic instance degrades to an
uninterpreted symbol rather than being silently mistranslated. -/
def hasCanonicalInstance (e : Expr) (i : Nat) : TranslateM Bool := do
  let args := e.getAppArgs
  let some inst := args[i]? | return false
  let instTy ← inferType inst
  try
    let canon ← synthInstance instTy
    isDefEq inst canon
  catch _ =>
    -- Synthesis failed: we cannot confirm the instance is standard, so treat it as
    -- non-canonical and let the term degrade to an uninterpreted symbol.
    return false

/-- A supported inductive we can emit as an SMT datatype: enumerations, simple
structures, self-recursive `List`- or tree-shaped types, and — via monomorphization —
*fully-applied parametric* types such as `Option Int`, `Int × Int`, `List Bool`.

`typeArgs` are the concrete parameter values the head is applied to (empty for a
non-parametric type). The type must be **ground** — no remaining type variables — so
the constructor field sorts are determined; a bare `List` with an un-instantiated
element type stays an opaque sort.

We require at least one constructor: SMT-LIB datatypes must be inhabited
(z3 rejects `(declare-datatypes ((E 0)) (()))`), and more fundamentally every SMT
sort is non-empty while `Empty` is not, so an empty Lean inductive cannot be
modelled faithfully and must stay an opaque sort (see `isEmptyType`). -/
def isSupportedDatatypeApp (n : Name) (typeArgs : Array Expr) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | return false
  -- Indices (true dependent families) are unsupported; parameters are fine once
  -- instantiated. The applied prefix must supply exactly the parameters.
  if iv.numIndices != 0 then return false
  if typeArgs.size != iv.numParams then return false
  if n == ``Nat || n == ``Int || n == ``Bool || n == ``String then return false
  if iv.ctors.isEmpty then return false
  -- A type *class* (`HAdd`, `Inhabited`, …) is not data: its fields are typically
  -- functions, and a value is an instance-dictionary chosen by synthesis, not
  -- something to reason about structurally. Keep classes opaque; this also stops a
  -- non-canonical operator instance from being datatype-encoded.
  if isClass env n then return false
  -- Every parameter argument must itself be a *type* (`Sort`), and ground — a
  -- remaining metavariable/fvar element type has no SMT sort. This is what keeps a
  -- polymorphic `List α` opaque while `List Int` is a real datatype.
  for a in typeArgs do
    let aty ← whnf (← inferType a)
    unless aty.isSort do return false
    if (← instantiateMVars a).hasExprMVar then return false
  -- Must live in `Type`, not `Prop` (propositions map to `Bool`). A
  -- universe-polymorphic declaration such as `PUnit : Sort u` reports its *generic*
  -- result as `.sort (u+1)` rather than `Type`, so accept a `.sort` whose level is
  -- not literally `0`; that admits `PUnit`/`Unit` while still excluding `Prop`.
  unless (match iv.type.getForallBody with
          | .sort l => !l.isZero
          | _ => false) do
    return false
  -- Every constructor field, *instantiated at `typeArgs`*, must be translatable to a
  -- non-function SMT sort. A field mentioning the datatype in a strictly positive,
  -- direct way (`T ā` itself) is fine; a *function-typed* field cannot be a datatype
  -- selector's range (SMT datatypes are first-order), so such a type stays opaque.
  -- Fields must also be data, not proofs (a `Prop` field has no SMT sort).
  iv.ctors.allM fun ctorName => do
    let ci ← getConstInfoCtor ctorName
    let ctorTy ← instantiateForall ci.type typeArgs
    forallTelescopeReducing ctorTy fun args _ =>
      args.allM fun a => do
        let ty ← whnf (← inferType a)
        if ty.isForall then return false
        if ← isProp ty then return false
        return true

/-- `isSupportedDatatypeApp` for a fully-applied type expression. -/
def supportedDatatypeType? (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let e ← whnf e
  let .const n _ := e.getAppFn | return none
  let args := e.getAppArgs
  if ← isSupportedDatatypeApp n args then return some (n, args) else return none


/-- Whether `ty` is an *uninhabited* Lean type, which SMT cannot model: every SMT
sort is non-empty, so `∀ x : Empty, P` (vacuously true) would translate to the
much stronger `(forall ((x S)) P)`.

Detected structurally: a `Type`-valued inductive with no constructors. `Prop`s are
not affected (they map to `Bool`). -/
def isEmptyType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  let .const n _ := ty.getAppFn | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  return iv.ctors.isEmpty && iv.numIndices == 0

/-- Names of the SMT constructor / selector for a Lean constructor.

These must be **globally unique across datatypes**, not just within one: two
distinct Lean structures both named `mk` (the default anonymous-constructor name)
would otherwise emit two `mk`s and two `mk_sel0`s into one script, silently
conflating the two types' constructors and selectors. We therefore key on the
datatype's *allocated SMT sort symbol*, which `symbolFor` already guarantees to be
unique, rather than on the bare Lean name. -/
def ctorSymbol (sortName : String) (ctorName : Name) : String :=
  s!"{sortName}_{nameHint ctorName}"

def selSymbol (sortName : String) (ctorName : Name) (i : Nat) : String :=
  s!"{sortName}_{nameHint ctorName}_{i}"

/-- The SMT tester `((_ is C) x)`. -/
def testerApp (ctorSym : String) (x : SMT.Term) : SMT.Term :=
  .app (.indexed "is" #[.inl ctorSym]) #[x]

/-- The well-formedness predicate symbol for a datatype sort. -/
def wfSymbol (sortName : String) : String := s!"wf_{sortName}"

/-- Whether `e` is an application of an overloaded arithmetic/comparison operator
whose instance argument is **not** the one instance synthesis would pick.

The recognizers for `+`, `*`, `≤`, `max`, … match on the head symbol, which commits
them to the standard interpretation of that symbol. A non-standard instance means the
operator denotes a different function, so the term must fall through to the
uninterpreted path rather than being translated as SMT arithmetic.

The instance is argument 3 for the heterogeneous classes (`HAdd`/`HMul`/`HSub`/…,
whose signature is `{α β γ} [inst] a b`), argument 1 for the homogeneous ones
(`LE`/`LT`/`Neg`/`Max`/`Min`, `{α} [inst] a b`). -/
def isNonCanonicalOverload (e : Expr) : TranslateM Bool := do
  let .const fname _ := e.getAppFn | return false
  let instIdx : Option Nat :=
    if fname == ``HAdd.hAdd || fname == ``HMul.hMul || fname == ``HSub.hSub
       || fname == ``HDiv.hDiv || fname == ``HMod.hMod || fname == ``HAnd.hAnd
       || fname == ``HOr.hOr || fname == ``HXor.hXor || fname == ``HAppend.hAppend
       || fname == ``HShiftLeft.hShiftLeft || fname == ``HShiftRight.hShiftRight then
      some 3
    else if fname == ``LE.le || fname == ``LT.lt || fname == ``GE.ge || fname == ``GT.gt
            || fname == ``Neg.neg || fname == ``Complement.complement
            || fname == ``Max.max || fname == ``Min.min then
      some 1
    else
      none
  let some i := instIdx | return false
  return !(← hasCanonicalInstance e i)

/-- The `declare` callback exposed to handlers: emit commands from a thunk once
per key, returning a stable symbol. -/
partial def declareViaThunk (key hint : String)
    (gen : String → TranslateM (Array SMT.Command)) : TranslateM String := do
  let name ← TranslateM.symbolFor key hint
  if !(← declaredFun name) then
    let cmds ← gen name
    for c in cmds do TranslateM.emitCommand c
    markFunDeclared name
  return name

mutual
  /-- Sort translation. Interpreted Lean types map to SMT theory sorts; supported
  inductives are declared as SMT datatypes; everything else becomes a declared
  nullary uninterpreted sort keyed by the type's canonical form.

  User `@[crush_translate_sort]` handlers get first refusal (like term handlers in
  `emitTerm`), so a user can retarget a Lean type to a theory sort — e.g. a finite map
  to SMT's `(Array K V)`. Skipped wholesale when none are registered. -/
  partial def emitSort (e : Expr) : TranslateM SSort := do
    let e ← whnf e
    if ← hasSortHandlers then
      let (fn, args) := getAppFnArgs' e
      let ctx : TranslationCtx := {
        fn, args
        emitTerm := emitTerm
        emitSort := emitSort
        declare  := declareViaThunk }
      for h in (← getSortHandlers) do
        if let some s ← h ctx then
          return s
    match e with
    | .const ``Bool _ => return .app (.symb "Bool") #[]
    | .const ``Nat _  => return .app (.symb "Int") #[]
    | .const ``Int _  => return .app (.symb "Int") #[]
    | .const ``String _ => return .app (.symb "String") #[]
    -- `Prop` is the sort of propositions and maps to SMT `Bool`. A *larger* universe
    -- does not: mapping `Type` to `Bool` would put every Lean type into a
    -- two-element set, so three distinct types would have to collide and the solver
    -- could "prove" type equalities that are false. Such a position gets an opaque
    -- sort instead, which is uninterpreted and therefore sound.
    | .sort l => if l.isZero then return .app (.symb "Bool") #[]
                 else declareUninterpretedSort e
    | _ =>
    -- `BitVec w` at a statically-known width maps to the indexed sort
    -- `(_ BitVec w)`. A symbolic width has no SMT counterpart, so it falls through
    -- to an opaque sort (where `BitVec` ops will not be recognized either).
    match ← bvWidthOfType? e with
    | some w => return bvSort w
    | none =>
    -- An arrow type is a *function sort*: an uninterpreted `Fn` sort paired with an
    -- `app` symbol (higher-order encoding). Emitting it as a plain opaque sort is
    -- what made function-typed bound variables unsound: the variable ended up
    -- disconnected from its own quantifier.
    if (← whnf e).isArrow then
      -- `native` mode uses the solver's own function sort `(-> σ τ)`; the other
      -- modes introduce an uninterpreted `Fn` sort plus an `app` symbol.
      if (← TranslateM.getConfig).hoMode == .native then
        let some shape ← arrowShape? e
          | throwError "crush: internal — non-arrow in arrow branch: {e}"
        return nativeArrowSort (← shape.args.mapM emitSort) (← emitSort shape.res)
      let (sort, _) ← declareArrowSort e
      return sort
    -- A supported inductive — including a fully-applied parametric one like
    -- `Option Int` or `Int × Int` — becomes a (monomorphized) SMT datatype. The
    -- instantiation `(n, typeArgs)` keys a distinct SMT sort per element type, so
    -- `Option Int` and `Option Bool` never share a sort.
    match ← supportedDatatypeType? e with
    | some (n, typeArgs) => return .app (.symb (← declareDatatype n typeArgs)) #[]
    | none => declareUninterpretedSort e

  /-- Declare the `Fn` sort and `app` symbol for an arrow type `σ₁ → … → τ`, once.
  Returns the sort and its `app` symbol name.

  The `app` symbol is *n*-ary over the flattened argument list rather than a chain
  of unary applies: `Int → Int → Bool` gets `app (Fn Int Int) Int → Bool` in one
  step. This keeps the encoding small for the common fully-applied case. Partial
  application is handled separately (`partialApp?`) by materializing the
  intermediate closure. -/
  partial def declareArrowSort (ty : Expr) : TranslateM (SSort × String) := do
    let key ← arrowKey ty
    let sortName ← TranslateM.symbolFor key "Fn"
    let sort := SSort.app (.symb sortName) #[]
    let aKey ← appKey ty
    let appName ← TranslateM.symbolFor aKey s!"app_{sortName}"
    if !(← declaredSort sortName) then
      markSortDeclared sortName
      TranslateM.emitCommand (.declSort sortName 0)
      -- `app` takes the function value plus the flattened argument sorts.
      let some shape ← arrowShape? ty
        | throwError "crush: internal — `declareArrowSort` on a non-arrow {ty}"
      let argSorts ← shape.args.mapM emitSort
      let resSort ← emitSort shape.res
      TranslateM.emitCommand (.declFun appName (#[sort] ++ argSorts) resSort)
      markFunDeclared appName
    return (sort, appName)

  /-- Emit the extensionality axiom for an arrow sort, on demand and once:

  ```
  (assert (forall ((a Fn) (b Fn))
    (=> (forall (x̄) (= (app a x̄) (app b x̄))) (= a b))))
  ```

  Only needed when an equation between function-typed terms appears. Verified
  load-bearing: `∀ x, f x = g x ⊢ f = g` is `sat` without it, `unsat` with it. It
  is a costly axiom (a quantifier alternation), hence emitted lazily rather than
  for every arrow sort that happens to occur. -/
  partial def emitExtensionality (ty : Expr) : TranslateM Unit := do
    let (sort, appName) ← declareArrowSort ty
    let .app (.symb sortName) _ := sort
      | return ()
    if ← declaredFun (extKey sortName) then return
    markFunDeclared (extKey sortName)
    let some shape ← arrowShape? ty | return ()
    let a ← TranslateM.freshSymbol "ext_a"
    let b ← TranslateM.freshSymbol "ext_b"
    let mut binders : Array (String × SSort) := #[]
    let mut argRefs : Array SMT.Term := #[]
    for argTy in shape.args do
      let v ← TranslateM.freshSymbol "ext_x"
      binders := binders.push (v, ← emitSort argTy)
      argRefs := argRefs.push (.const v)
    let appA := SMT.Term.app (.symb appName) (#[SMT.Term.const a] ++ argRefs)
    let appB := SMT.Term.app (.symb appName) (#[SMT.Term.const b] ++ argRefs)
    let premise := SMT.Term.forallE binders (.symbApp "=" #[appA, appB])
    TranslateM.emitCommand (.assert
      (.forallE #[(a, sort), (b, sort)]
        (.symbApp "=>" #[premise, .symbApp "=" #[.const a, .const b]])))

  /-- Translate a λ-abstraction into a *closure*.

  `fun x => body[x, ȳ]` with captured free variables `ȳ` becomes a closure
  constructor `clo_k : (sorts of ȳ) → Fn` plus the defining axiom

  ```
  (assert (forall (ȳ x̄) (= (app (clo_k ȳ) x̄) body[x̄, ȳ])))
  ```

  Captures are the λ's free fvars that are themselves SMT-bound (quantifier
  variables); free fvars from the local context are already global symbols and need
  no parameterization. Keyed on the λ term, so repeated/α-equivalent λs share one
  closure. -/
  partial def emitClosure (lam : Expr) : TranslateM SMT.Term := do
    let lamTy ← whnf (← inferType lam)
    let (_, appName) ← declareArrowSort lamTy
    let some shape ← arrowShape? lamTy
      | throwError "crush: internal — closure for non-arrow type {lamTy}"
    let key ← closureKey lam
    -- Captured SMT-bound variables, in a deterministic order.
    let st ← get
    let captures := (collectFVars lam).filter fun fid =>
      st.boundVars.contains fid || st.funVars.contains fid
    if let some existing := st.atomToName.get? key then
      -- Already declared: rebuild the application from the recorded captures.
      let capArgs ← captures.mapM fun fid => emitTerm (.fvar fid)
      return if capArgs.isEmpty then .const existing
             else .app (.symb existing) capArgs
    let cloName ← TranslateM.symbolFor key "clo"
    let capSorts ← captures.mapM fun fid => do emitSort (← fid.getType)
    let (arrowSort, _) ← declareArrowSort lamTy
    TranslateM.emitCommand (.declFun cloName capSorts arrowSort)
    markFunDeclared cloName
    -- The defining axiom. Fresh SMT variables for the λ's own parameters; the
    -- captures are quantified too so the axiom holds for every instantiation.
    let mut binders : Array (String × SSort) := #[]
    let mut capRefs : Array SMT.Term := #[]
    for fid in captures do
      let nm := (st.boundVars.get? fid).getD ((st.funVars.get? fid).getD "c")
      let fty ← fid.getType
      binders := binders.push (nm, ← emitSort fty)
      capRefs := capRefs.push (.const nm)
    let cloApp := if capRefs.isEmpty then SMT.Term.const cloName
                  else SMT.Term.app (.symb cloName) capRefs
    -- Enter the λ's binders with real fvars so the body becomes closed.
    let (paramBinders, bodyTerm) ← emitLambdaBody lam shape
    let lhs := SMT.Term.app (.symb appName)
      (#[cloApp] ++ paramBinders.map (fun (n, _) => SMT.Term.const n))
    let axiomBody := SMT.Term.symbApp "=" #[lhs, bodyTerm]
    let allBinders := binders ++ paramBinders
    TranslateM.emitCommand (.assert
      (if allBinders.isEmpty then axiomBody else .forallE allBinders axiomBody))
    let capArgs ← captures.mapM fun fid => emitTerm (.fvar fid)
    return if capArgs.isEmpty then .const cloName
           else .app (.symb cloName) capArgs

  /-- Introduce fresh SMT-named binders for a λ's parameters and translate its body
  under them. Returns the binders and the translated body. -/
  partial def emitLambdaBody (lam : Expr) (shape : ArrowShape) :
      TranslateM (Array (String × SSort) × SMT.Term) := do
    let mut names : Array String := #[]
    for _ in shape.args do
      names := names.push (← TranslateM.freshSymbol "lx")
    let mut binders : Array (String × SSort) := #[]
    for (n, argTy) in names.zip shape.args do
      binders := binders.push (n, ← emitSort argTy)
    -- Instantiate the λ at fresh fvars bound to the SMT names.
    let body ← withLambdaFVars lam names shape.args
    return (binders, body)

  /-- Enter a λ's binders with fresh fvars mapped to the given SMT names, and
  translate the resulting body. A function-typed parameter is registered as a
  `funVar` so its applications route through the appropriate `app` symbol. -/
  partial def withLambdaFVars (lam : Expr) (names : Array String)
      (argTys : Array Expr) : TranslateM SMT.Term := do
    let rec go (i : Nat) (e : Expr) (acc : Array Expr) : TranslateM SMT.Term := do
      if i ≥ names.size then
        emitTerm (e.instantiateRev acc)
      else
        let nm := names[i]!
        let ty := argTys[i]!
        withLocalDeclD (Name.mkSimple nm) ty fun x => do
          let bind (k : TranslateM SMT.Term) : TranslateM SMT.Term :=
            TranslateM.withBoundVar x.fvarId! nm k
          -- A function-typed parameter routes through its `app` symbol — except in
          -- native mode, where it is applied directly and declaring an `Fn` sort
          -- would leave dead declarations in the script.
          if (← whnf ty).isArrow && (← TranslateM.getConfig).hoMode != .native then
            let (_, appSym) ← declareArrowSort ty
            bind (TranslateM.withFunVar x.fvarId! appSym (go (i + 1) e (acc.push x)))
          else if (← whnf ty).isArrow then
            bind (TranslateM.withFunVar x.fvarId! nm (go (i + 1) e (acc.push x)))
          else
            bind (go (i + 1) e (acc.push x))
    -- Peel the λ binders themselves.
    let body := (← lambdaTelescopeBody lam names.size)
    go 0 body #[]

  /-- The body of `lam` under `n` peeled λ binders, as an open term with loose
  bvars (to be instantiated by `withLambdaFVars`). -/
  partial def lambdaTelescopeBody (lam : Expr) (n : Nat) : TranslateM Expr := do
    let mut e := lam
    for _ in [0:n] do
      match e with
      | .lam _ _ b _ => e := b
      | _ =>
        -- Not syntactically a λ (e.g. a partially-applied constant): η-expand.
        return e
    return e

  /-- All free variables of `e`, in first-occurrence order. -/
  partial def collectFVars (e : Expr) : Array FVarId :=
    go e #[]
  where
    go (e : Expr) (acc : Array FVarId) : Array FVarId :=
      match e with
      | .fvar fid => if acc.contains fid then acc else acc.push fid
      | .app f a => go a (go f acc)
      | .lam _ t b _ => go b (go t acc)
      | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b => go b acc
      | .proj _ _ b => go b acc
      | _ => acc

  /-- Emit a `declare-sort` for an opaque type, once. -/
  partial def declareUninterpretedSort (e : Expr) : TranslateM SSort := do
    let key := toString (← ppExpr e)
    let hint := match e with | .const n _ => nameHint n | _ => "s"
    let name ← TranslateM.symbolFor key hint
    if !(← declaredSort name) then
      TranslateM.emitCommand (.declSort name 0)
      markSortDeclared name
    return .app (.symb name) #[]

  /-- Declare a supported inductive as an SMT datatype (idempotent); return its
  sort symbol. One SMT constructor per Lean constructor, positional selectors.

  Two subtleties, both soundness-relevant:

  * Constructor and selector symbols are qualified by the datatype's SMT sort name
    (`ctorSymbol`/`selSymbol`) so distinct Lean types with same-named constructors
    (`mk`, `mk`) cannot collide in one script.

  * SMT datatypes are **freely generated over their field sorts**. A `Nat` field is
    encoded as `Int`, so the SMT type contains values with *negative* fields that
    have no Lean counterpart. Left unguarded this is unsound in the dangerous
    direction: the true hypothesis `∀ p : PN, p.x ≥ 0` becomes unsatisfiable, from
    which the solver derives `False`. We therefore emit a well-formedness predicate
    `wf_T` characterizing the image of the Lean type, and *guard every quantifier
    over `T`* with it (see `quantifier`/`guardSort`). -/
  partial def declareDatatype (n : Name) (typeArgs : Array Expr := #[]) :
      TranslateM String := do
    -- Key on the head *and* its instantiation, so `Option Int` and `Option Bool`
    -- get distinct sorts, constructors, and selectors. The key uses the
    -- pretty-printed type arguments, matching how opaque sorts are keyed.
    let argKey ← if typeArgs.isEmpty then pure ""
                 else do
                   let ks ← typeArgs.mapM fun a => do pure (toString (← ppExpr a))
                   pure s!"@{String.intercalate "," ks.toList}"
    let key := s!"__datatype__{n}{argKey}"
    if let some name := (← get).atomToName.get? key then
      return name
    let sortName ← TranslateM.symbolFor key (nameHint n)
    -- Register the sort name *before* translating field sorts: a recursive
    -- datatype's fields mention the type (at this same instantiation), and must
    -- resolve to this symbol rather than recursing forever. `declareDatatype` is
    -- idempotent on the key, so a recursive occurrence returns `sortName` directly.
    markSortDeclared sortName
    let iv ← getConstInfoInduct n
    let mut ctorDecls : Array CtorDecl := #[]
    -- Field descriptors for the wf axiom: per ctor, the selectors needing a guard.
    let mut wfParts : Array (String × Array (String × Expr)) := #[]
    for ctorName in iv.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      -- Instantiate the constructor's type at the datatype's parameters, so each
      -- field type is ground (`Option.some : α → Option α` becomes `Int → Option Int`
      -- at `typeArgs = #[Int]`).
      let ctorTy ← instantiateForall ctorInfo.type typeArgs
      let (selDecls, guards) ← forallTelescopeReducing ctorTy fun args _ => do
        let mut sels : Array (String × SSort) := #[]
        let mut gs : Array (String × Expr) := #[]
        for i in [0:args.size] do
          let fieldTy ← inferType args[i]!
          let s ← emitSort fieldTy
          let selName := selSymbol sortName ctorName i
          sels := sels.push (selName, s)
          if (← needsWFGuard fieldTy) then
            gs := gs.push (selName, fieldTy)
        return (sels, gs)
      ctorDecls := ctorDecls.push { name := ctorSymbol sortName ctorName, selDecls }
      wfParts := wfParts.push (ctorSymbol sortName ctorName, guards)
    TranslateM.emitCommand (.declDatatypes #[(sortName, 0, { ctors := ctorDecls })])
    emitDatatypeWF sortName wfParts
    return sortName

  /-- Whether values of `ty` occupy a *proper subset* of their SMT sort, so a
  quantifier over them needs a guard. True for `Nat` (encoded as `Int`) and for any
  datatype that transitively contains such a field. -/
  partial def needsWFGuard (ty : Expr) : TranslateM Bool := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then return true
    let some (n, typeArgs) ← supportedDatatypeType? ty | return false
    -- Guard against cycles: a recursive datatype needs a guard iff some field does,
    -- and self-reference alone contributes nothing new. Fields are examined at this
    -- instantiation, so a `Nat` reached only through the type parameter (`Option Nat`)
    -- is caught, while `Option Int` is not.
    let iv ← getConstInfoInduct n
    iv.ctors.anyM fun ctorName => do
      let ci ← getConstInfoCtor ctorName
      let ctorTy ← instantiateForall ci.type typeArgs
      forallTelescopeReducing ctorTy fun args _ =>
        args.anyM fun a => do
          let fty ← whnf (← inferType a)
          if fty.getAppFn.isConstOf n then return false  -- self-reference
          needsWFGuard fty

  /-- Emit `wf_T`'s declaration and defining axiom, once per datatype.

  The axiom is stated in *selector* form per constructor,

  ```
  (declare-fun wf_T (T) Bool)
  (assert (forall ((x T)) (= (wf_T x)
    (and (=> ((_ is C₁) x) ⟨guards on C₁'s fields of x⟩) …))))
  ```

  which z3 handles far better than the constructor-applied form. When no field
  needs a guard the predicate is defined as constantly `true`, so the guard added
  at each quantifier is trivially discharged and costs nothing. -/
  partial def emitDatatypeWF (sortName : String)
      (parts : Array (String × Array (String × Expr))) : TranslateM Unit := do
    let wf := wfSymbol sortName
    if ← declaredFun wf then return
    markFunDeclared wf
    let sort := SSort.app (.symb sortName) #[]
    TranslateM.emitCommand (.declFun wf #[sort] (.app (.symb "Bool") #[]))
    let v ← TranslateM.freshSymbol "d"
    let x := SMT.Term.const v
    let mut conjuncts : Array SMT.Term := #[]
    for (ctorSym, guards) in parts do
      if guards.isEmpty then continue
      let mut fieldConds : Array SMT.Term := #[]
      for (selName, fieldTy) in guards do
        let selApp := SMT.Term.app (.symb selName) #[x]
        if let some c ← wfCondition fieldTy selApp then
          fieldConds := fieldConds.push c
      if fieldConds.isEmpty then continue
      let body := if fieldConds.size == 1 then fieldConds[0]!
                  else .symbApp "and" fieldConds
      conjuncts := conjuncts.push (.symbApp "=>" #[testerApp ctorSym x, body])
    let rhs :=
      if conjuncts.isEmpty then SMT.Term.lit (.bool true)
      else if conjuncts.size == 1 then conjuncts[0]!
      else .symbApp "and" conjuncts
    TranslateM.emitCommand
      (.assert (.forallE #[(v, sort)] (.symbApp "=" #[.app (.symb wf) #[x], rhs])))

  /-- The well-formedness condition on an SMT term of Lean type `ty`: `≥ 0` for
  `Nat`, `wf_T` for a guarded datatype, `none` when nothing is needed. -/
  partial def wfCondition (ty : Expr) (t : SMT.Term) : TranslateM (Option SMT.Term) := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then
      return some (.symbApp ">=" #[t, .lit (.num 0)])
    let some (n, typeArgs) ← supportedDatatypeType? ty | return none
    if !(← needsWFGuard ty) then return none
    let sortName ← declareDatatype n typeArgs
    return some (.app (.symb (wfSymbol sortName)) #[t])

  /-- Translate a term, trying user handlers first.

  Dispatch order, and why: a quantifier-bound variable resolves to its SMT name
  first (it is never a declaration); then **user `@[crush_translate]` handlers**,
  so a user can override *any* built-in mapping for their own constant. The
  extensibility contract is that user handlers override built-ins for the same
  constant — there is no privileged built-in path — so the handlers must get first
  refusal. Only if no handler claims the term do the built-in higher-order and
  first-order structural paths run. The handler loop is skipped wholesale when none
  are registered (`hasTranslationHandlers`), so the common case pays a single
  array-empty check. -/
  partial def emitTerm (e : Expr) : TranslateM SMT.Term := do
    let e ← instantiateMVars e
    -- A quantifier-bound variable renders as its SMT name, never a declaration.
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- User handlers get first refusal on the applied head, so they override the
    -- built-in structural/theory mappings below rather than being shadowed by them.
    if ← hasTranslationHandlers then
      let (fn, args) := getAppFnArgs' e
      let ctx : TranslationCtx := {
        fn, args
        emitTerm := emitTerm
        emitSort := emitSort
        declare  := declareViaThunk }
      for h in (← getTranslationHandlers) do
        if let some t ← h ctx then
          return t
    -- Higher-order forms, before the first-order structural path.
    if let some t ← hoTerm? e then
      return t
    -- Fast path for the structural logical/theory core.
    match ← structural? e with
    | some t => return t
    | none =>
      let (fn, args) := getAppFnArgs' e
      -- A constructor of a supported datatype → the SMT constructor symbol.
      if let some t ← ctorApp? fn args then
        return t
      -- A structure projection → the SMT selector.
      if let some t ← projApp? fn args then
        return t
      -- Default: uninterpreted function/atom applied to translated args.
      defaultApp fn args

  /-- Higher-order forms: λ-abstractions, applications of function-*valued* terms,
  and equations between function-typed terms. Returns `none` for anything the
  first-order path should handle.

  This is the entry point for the encoding described in `HOEncoding.lean`, and the
  fix for the false-`unsat` that arose when a function-typed bound variable was
  declared as an unrelated `declare-fun`. -/
  partial def hoTerm? (e : Expr) : TranslateM (Option SMT.Term) := do
    let mode := (← TranslateM.getConfig).hoMode
    -- (1) A λ becomes a closure with a defining axiom (or a native `lambda`).
    if e.isLambda then
      if mode == .native then
        return some (← emitNativeLambda e)
      return some (← emitClosure e)
    -- (2) An application whose head is a function-typed *bound variable* must route
    -- through that arrow sort's `app` symbol. Emitting `(f x)` directly would
    -- declare `f` as a fresh function unrelated to the quantified variable.
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .fvar fid := fn then
      if let some appSym ← TranslateM.funVar? fid then
        if args.isEmpty then
          -- The bare function value: its SMT name.
          if let some vname ← TranslateM.boundVar? fid then
            return some (.const vname)
          return none
        let some vname ← TranslateM.boundVar? fid | return none
        let sargs ← args.mapM emitTerm
        -- In native mode the variable *is* a function: apply it directly.
        if mode == .native then
          return some (.app (.symb vname) sargs)
        return some (.app (.symb appSym) (#[.const vname] ++ sargs))
    -- (3) An equation between function-typed terms needs extensionality to be
    -- provable, and needs both sides encoded as `Fn` values rather than symbols.
    match_expr e with
    | Eq ty a b =>
      if (← whnf ty).isArrow then
        -- Native mode gets extensionality from the solver itself; the encoded modes
        -- need it asserted explicitly (verified load-bearing).
        if mode != .native then
          emitExtensionality ty
        return some (.symbApp "=" #[← emitFunValue a, ← emitFunValue b])
      return none
    | _ => return none

  /-- A native higher-order `lambda` term, for HO-capable backends. -/
  partial def emitNativeLambda (lam : Expr) : TranslateM SMT.Term := do
    let lamTy ← whnf (← inferType lam)
    let some shape ← arrowShape? lamTy
      | throwError "crush: internal — native lambda of non-arrow type {lamTy}"
    let (binders, body) ← emitLambdaBody lam shape
    return .lam binders body

  /-- Translate a term of function type as an `Fn`-sorted *value* (not as a symbol
  applied to arguments). A λ becomes its closure; a first-order function constant
  becomes a closure wrapping it, so that `f = g` compares `Fn` values. -/
  partial def emitFunValue (e : Expr) : TranslateM SMT.Term := do
    let e ← instantiateMVars e
    let mode := (← TranslateM.getConfig).hoMode
    if e.isLambda then
      return ← if mode == .native then emitNativeLambda e else emitClosure e
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- A function constant/fvar used as a value: η-expand it so it inhabits the
    -- function sort. `f` becomes `fun x => f x` — a closure (encoded modes) or a
    -- native `lambda`.
    let ty ← whnf (← inferType e)
    let some shape ← arrowShape? ty | return ← emitTerm e
    let etaLam ← mkLambdaFVars' shape.args e
    if mode == .native then emitNativeLambda etaLam else emitClosure etaLam

  /-- η-expand `f` to `fun x₁ … xₙ => f x₁ … xₙ` over the given argument types. -/
  partial def mkLambdaFVars' (argTys : Array Expr) (f : Expr) : TranslateM Expr := do
    let rec go (i : Nat) (acc : Array Expr) : TranslateM Expr := do
      if i ≥ argTys.size then
        Meta.mkLambdaFVars acc (mkAppN f acc)
      else
        withLocalDeclD (Name.mkSimple s!"eta{i}") argTys[i]! fun x =>
          go (i + 1) (acc.push x)
    go 0 #[]

  /-- If `fn` is a projection of a supported (possibly parametric) datatype,
  translate `fn s` to the SMT selector `<ctor>_sel<i> s`. The datatype instantiation
  is read off the structure argument's type, so `(p : Int × Int).1` selects from the
  monomorphized `Prod Int Int` sort. -/
  partial def projApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const pn _ := fn | return none
    let some info ← getProjectionFnInfo? pn | return none
    -- Projections take the structure as the argument after `info.numParams`.
    let some structArg := args[info.numParams]? | return none
    let structTy ← whnf (← inferType structArg)
    let some (_, typeArgs) ← supportedDatatypeType? structTy | return none
    let sortName ← declareDatatype info.ctorName.getPrefix typeArgs
    let sel := selSymbol sortName info.ctorName info.i
    let extraArgs := args.extract (info.numParams + 1) args.size
    let sarg ← emitTerm structArg
    let sextra ← extraArgs.mapM emitTerm
    return some (.app (.symb sel) (#[sarg] ++ sextra))

  /-- If `fn` is a constructor of a supported (possibly parametric) datatype,
  translate the application to the corresponding SMT constructor symbol applied to
  the *value* args (type parameters are dropped — they select the instantiation, not
  a field). The datatype is declared at that instantiation first. -/
  partial def ctorApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const cn _ := fn | return none
    let env ← getEnv
    let some (.ctorInfo ci) := env.find? cn | return none
    -- The applied constructor's result type carries the instantiation.
    let resTy ← whnf (← inferType (mkAppN fn args))
    let some (_, typeArgs) ← supportedDatatypeType? resTy | return none
    let sortName ← declareDatatype ci.induct typeArgs
    -- Drop the leading type-parameter arguments; keep the value fields.
    let valueArgs := args.extract ci.numParams args.size
    let sargs ← valueArgs.mapM emitTerm
    return some (.app (.symb (ctorSymbol sortName cn)) sargs)

  /-- Recognize the built-in logical/arithmetic structure. Returns `none` to let
  handlers / the default path take over. -/
  partial def structural? (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .const ``True _  => return some (.lit (.bool true))
    | .const ``False _ => return some (.lit (.bool false))
    | .const ``Bool.true _  => return some (.lit (.bool true))
    | .const ``Bool.false _ => return some (.lit (.bool false))
    | .lit (.strVal s) => return some (.lit (.str s))
    | _ =>
    -- Every recognizer below that matches an overloaded operator
    -- (`HAdd.hAdd`, `LE.le`, `max`, …) assumes the *standard* instance. A
    -- user-supplied instance makes the operator mean something else entirely —
    -- `⟨fun _ _ => 99⟩ : HAdd Int Int Int` is legal, and then `1 + 2 = 99` — so
    -- translating it as SMT `+` proves false goals. Bail out to the uninterpreted
    -- path when the instance is not the one synthesis would choose.
    if ← isNonCanonicalOverload e then return none
    match e with
    | _ =>
    -- Bit-vector and string theories, which need type-directed dispatch.
    match ← bitvecTerm? e with
    | some t => return some t
    | none =>
    match ← stringTerm? e with
    | some t => return some t
    | none =>
    -- Numeric literals: `@OfNat.ofNat _ n _` and negation.
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      match ← getNatLit? e with
      | some n => return some (.lit (.num n))
      | none => return none
    | Neg.neg _ _ a =>
      return some (.symbApp "-" #[← emitTerm a])
    | HDiv.hDiv _ _ _ _ a b =>
      -- SMT-LIB leaves `(div x 0)` to the model while Lean pins it to `0`; pin it
      -- too so the encoding is exact (see `intDivGuard`).
      return some (intDivGuard "div" (← emitTerm a) (← emitTerm b))
    | HMod.hMod _ _ _ _ a b =>
      return some (intDivGuard "mod" (← emitTerm a) (← emitTerm b))
    | _ =>
    match_expr e with
    | And a b => return some (.symbApp "and" #[← emitTerm a, ← emitTerm b])
    | Or a b  => return some (.symbApp "or" #[← emitTerm a, ← emitTerm b])
    | Not a   => return some (.symbApp "not" #[← emitTerm a])
    -- The `Bool`-valued connectives, which are ordinary functions (`not`/`and`/…)
    -- rather than the `Prop` classes above. Since `Prop` and `Bool` share the SMT
    -- `Bool` sort, they map to the same operators — but they are distinct `Expr`s
    -- and must each be recognized, or they become uninterpreted symbols.
    | not a   => return some (.symbApp "not" #[← emitTerm a])
    | and a b => return some (.symbApp "and" #[← emitTerm a, ← emitTerm b])
    | or a b  => return some (.symbApp "or" #[← emitTerm a, ← emitTerm b])
    | xor a b => return some (.symbApp "xor" #[← emitTerm a, ← emitTerm b])
    | bne _ _ a b => return some (.symbApp "not" #[.symbApp "=" #[← emitTerm a, ← emitTerm b]])
    | BEq.beq _ _ a b => return some (.symbApp "=" #[← emitTerm a, ← emitTerm b])
    | Iff a b => return some (.symbApp "=" #[← emitTerm a, ← emitTerm b])
    | Eq _ a b => return some (.symbApp "=" #[← emitTerm a, ← emitTerm b])
    | Ne _ a b => return some (.symbApp "not" #[.symbApp "=" #[← emitTerm a, ← emitTerm b]])
    | HAdd.hAdd _ _ _ _ a b => return some (.symbApp "+" #[← emitTerm a, ← emitTerm b])
    | HMul.hMul _ _ _ _ a b => return some (.symbApp "*" #[← emitTerm a, ← emitTerm b])
    | HSub.hSub _ _ _ _ a b =>
      -- `Nat` subtraction truncates at 0: `a - b = if a >= b then a - b else 0`.
      -- Encoding it as plain SMT `-` (which can go negative) is unsound.
      let sa ← emitTerm a
      let sb ← emitTerm b
      if (← isNatTyped e) then
        return some (.symbApp "ite"
          #[.symbApp ">=" #[sa, sb], .symbApp "-" #[sa, sb], .lit (.num 0)])
      else
        return some (.symbApp "-" #[sa, sb])
    -- SMT-LIB has no `max`/`min`, so they expand to an `ite`. Both are translated
    -- for whatever ordered sort the arguments have, so the `Nat` guard and the
    -- `BitVec` dispatch above still apply to the operands.
    | max _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (.symbApp "ite" #[.symbApp ">=" #[sa, sb], sa, sb])
    | min _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (.symbApp "ite" #[.symbApp "<=" #[sa, sb], sa, sb])
    -- `Nat.succ n` is `n + 1`; it appears from literals and from recursors.
    | Nat.succ a => return some (.symbApp "+" #[← emitTerm a, .lit (.num 1)])
    -- `decide p` is `p` itself once `Prop` is encoded as `Bool`.
    | decide p _ => return some (← emitTerm p)
    -- `Nat.cast` is the identity in this encoding *only* when the target is `Int`
    -- (or `Nat`), since `Nat` is already represented as a non-negative `Int`. For
    -- any other `NatCast` instance the coercion is an arbitrary function — it may
    -- collapse values, as `⟨fun _ => ⟨0⟩⟩` does — so treating it as the identity
    -- imports `Int`'s distinctness and lets the solver "prove" that equal values
    -- differ. Fall through to an uninterpreted symbol instead, which keeps
    -- congruence without assuming injectivity.
    | Nat.cast target _ a =>
      let target ← whnf target
      if target.isConstOf ``Int || target.isConstOf ``Nat then
        return some (← emitTerm a)
      else
        return none
    | LE.le _ _ a b => return some (.symbApp "<=" #[← emitTerm a, ← emitTerm b])
    | LT.lt _ _ a b => return some (.symbApp "<" #[← emitTerm a, ← emitTerm b])
    | GE.ge _ _ a b => return some (.symbApp ">=" #[← emitTerm a, ← emitTerm b])
    | GT.gt _ _ a b => return some (.symbApp ">" #[← emitTerm a, ← emitTerm b])
    | ite _ c _ a b =>
      -- `if c then a else b`; the condition `c : Prop` becomes an SMT Bool term.
      return some (.symbApp "ite" #[← emitTerm c, ← emitTerm a, ← emitTerm b])
    | cond _ b t e =>
      -- `Bool.cond`/`cond` with a `Bool` scrutinee.
      return some (.symbApp "ite" #[← emitTerm b, ← emitTerm t, ← emitTerm e])
    | _ =>
      -- Implication and quantifiers need binder handling.
      if e.isArrow then
        let some t ← tryImplication e | return none
        return some t
      match e with
      | .forallE _ ty body _ =>
        if (← isProp ty) then
          -- `∀ (h : p), q`. When `h` does not occur in `q` this is the implication
          -- `p ⇒ q`. When it *does* occur the binder is a genuine dependency on a
          -- proof — `∀ n, ∀ hn : n > 0, f n hn = n` — and the body cannot be
          -- translated without it, since SMT has no proof terms. Introduce a real
          -- fvar so the body is closed; proof-typed arguments are then dropped by
          -- `defaultApp`. Passing the open body straight to `emitTerm` used to leak
          -- a de Bruijn index as an "unexpected bound variable" error.
          let a ← emitTerm ty
          if body.hasLooseBVar 0 then
            let b ← withLocalDeclD `hp ty fun hp => emitTerm (body.instantiate1 hp)
            return some (.symbApp "=>" #[a, b])
          let b ← emitTerm body
          return some (.symbApp "=>" #[a, b])
        else
          quantifier true ty body
      | .app (.app (.const ``Exists _) _) (.lam _ ty body _) =>
        quantifier false ty body
      | .lit (.natVal n) => return some (.lit (.num n))
      | _ => return none

  /-- Bit-vector operations, dispatched on the *type* of the operands (the
  overloaded `HAdd`/`HDiv`/… classes are shared with `Int`, so the arithmetic
  recognizers must run after this one).

  Only statically-known widths are translated; a symbolic `BitVec w` has no SMT
  sort. Every case below was checked against both Lean and z3; the guarded
  divisions are the ones where the two genuinely disagree. -/
  partial def bitvecTerm? (e : Expr) : TranslateM (Option SMT.Term) := do
    -- `BitVec.ofNat w n` and numerals are handled first: they carry the width in
    -- the term rather than needing it from an operand.
    match_expr e with
    | BitVec.ofNat w n =>
      let some wv ← natValue? w | return none
      match ← natValue? n with
      | some nv => return some (bvLit wv nv)
      | none =>
        -- A *symbolic* argument needs the `int2bv` conversion rather than a literal.
        -- Both agree on wrap-around: `int2bv` reduces modulo `2 ^ w`, as
        -- `BitVec.ofNat` does. Without this the whole application became an
        -- uninterpreted symbol, losing every fact relating it to its argument.
        return some (.app (.indexed "int2bv" #[.inr wv]) #[← emitTerm n])
    | OfNat.ofNat ty n _ =>
      -- A `BitVec`-typed numeral must become a bit-vector literal, not an `Int`
      -- one; `OfNat` is shared with `Nat`/`Int`, so dispatch on the type.
      let some wv ← bvWidthOfType? ty | return none
      let some nv ← natValue? n | return none
      return some (bvLit wv nv)
    | _ =>
    -- Width of the result type, or (for predicates) of the first explicit operand.
    let args := e.getAppArgs
    let some w ← (do
      match ← bvWidthOfType? (← inferType e) with
      | some w => return some w
      | none =>
        -- A `BitVec`-valued predicate: find a `BitVec`-typed argument.
        for a in args do
          if let some w ← bvWidthOf? a then return some w
        return none) | return none
    let bin (op : String) (a b : Expr) : TranslateM (Option SMT.Term) := do
      return some (.symbApp op #[← emitTerm a, ← emitTerm b])
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b => bin "bvadd" a b
    | HSub.hSub _ _ _ _ a b => bin "bvsub" a b
    | HMul.hMul _ _ _ _ a b => bin "bvmul" a b
    | HAnd.hAnd _ _ _ _ a b => bin "bvand" a b
    | HOr.hOr _ _ _ _ a b   => bin "bvor" a b
    | HXor.hXor _ _ _ _ a b => bin "bvxor" a b
    | Complement.complement _ _ a => return some (.symbApp "bvnot" #[← emitTerm a])
    | Neg.neg _ _ a => return some (.symbApp "bvneg" #[← emitTerm a])
    -- `/` and `%` on `BitVec` are the *unsigned* operations, and Lean returns `0`
    -- at a zero divisor where SMT's `bvudiv` returns all-ones — hence the guard.
    -- `bvurem` already agrees with Lean (both return the dividend), so it is raw.
    | HDiv.hDiv _ _ _ _ a b => return some (bvDivGuard "bvudiv" w (← emitTerm a) (← emitTerm b))
    | HMod.hMod _ _ _ _ a b => bin "bvurem" a b
    -- The named forms of the operators above. Lean exposes both `x + y` (via the
    -- `HAdd` instance) and `BitVec.add x y`, and they are *different* `Expr`s, so
    -- recognizing only the notation leaves the named form to become an
    -- uninterpreted symbol — silently losing every fact about it.
    | BitVec.add _ a b => bin "bvadd" a b
    | BitVec.sub _ a b => bin "bvsub" a b
    | BitVec.mul _ a b => bin "bvmul" a b
    | BitVec.neg _ a => return some (.symbApp "bvneg" #[← emitTerm a])
    | BitVec.not _ a => return some (.symbApp "bvnot" #[← emitTerm a])
    | BitVec.and _ a b => bin "bvand" a b
    | BitVec.or _ a b  => bin "bvor" a b
    | BitVec.xor _ a b => bin "bvxor" a b
    | BitVec.udiv _ a b => return some (bvDivGuard "bvudiv" w (← emitTerm a) (← emitTerm b))
    | BitVec.umod _ a b => bin "bvurem" a b
    | BitVec.sdiv _ a b => return some (bvDivGuard "bvsdiv" w (← emitTerm a) (← emitTerm b))
    | BitVec.srem _ a b => bin "bvsrem" a b
    | BitVec.smod _ a b => bin "bvsmod" a b
    -- Comparisons. Lean's `<`/`≤` on `BitVec` are *unsigned* (verified:
    -- `(255 : BitVec 8) < 1` is `false`), so they map to `bvult`/`bvule`.
    | LT.lt _ _ a b => bin "bvult" a b
    | LE.le _ _ a b => bin "bvule" a b
    | GT.gt _ _ a b => bin "bvugt" a b
    | GE.ge _ _ a b => bin "bvuge" a b
    | BitVec.ult _ a b => bin "bvult" a b
    | BitVec.ule _ a b => bin "bvule" a b
    | BitVec.slt _ a b => bin "bvslt" a b
    | BitVec.sle _ a b => bin "bvsle" a b
    -- Shifts. The shift amount may be a `Nat` or a `BitVec`; SMT requires both
    -- operands at the same width, so a `Nat` amount is materialized as a literal
    -- (shift amounts ≥ width agree: both Lean and SMT yield 0 / sign-fill).
    | HShiftLeft.hShiftLeft _ _ _ _ a b => shiftOp "bvshl" w a b
    | HShiftRight.hShiftRight _ _ _ _ a b => shiftOp "bvlshr" w a b
    | BitVec.sshiftRight _ a b => shiftOp "bvashr" w a b
    | BitVec.shiftLeft _ a b => shiftOp "bvshl" w a b
    | BitVec.ushiftRight _ a b => shiftOp "bvlshr" w a b
    -- Rotations. SMT-LIB takes the amount as an *index*, not an operand, so only a
    -- literal amount is translatable. Both sides reduce the amount modulo the width
    -- (verified: `rotateLeft 10` on `BitVec 7` equals `rotateLeft 3` in Lean, and
    -- `(_ rotate_left 10)` agrees), so no explicit normalization is needed.
    | BitVec.rotateLeft _ a b => rotateOp "rotate_left" a b
    | BitVec.rotateRight _ a b => rotateOp "rotate_right" a b
    -- Width changes.
    | BitVec.setWidth _ target x =>
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize false xw tv (← emitTerm x))
    | BitVec.signExtend _ target x =>
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize true xw tv (← emitTerm x))
    | BitVec.extractLsb' _ start len x =>
      let some sv ← natValue? start | return none
      let some lv ← natValue? len | return none
      let some xw ← bvWidthOf? x | return none
      if lv == 0 then return none
      let sx ← emitTerm x
      -- Lean's `extractLsb'` zero-pads when `start + len` exceeds the width.
      if sv ≥ xw then return some (bvLit lv 0)
      let avail := xw - sv
      let sliced := bvExtract (min (sv + lv) xw - 1) sv sx
      return some (if lv ≤ avail then sliced else bvExtend false (lv - avail) sliced)
    | HAppend.hAppend _ _ _ _ a b =>
      -- `a ++ b` puts `a` in the high bits, matching SMT `concat` (verified:
      -- `(4 : BitVec 8) ++ (5 : BitVec 4) = 0x045#12`).
      return some (.symbApp "concat" #[← emitTerm a, ← emitTerm b])
    -- Bridges between bit-vectors and the integers. `toNat` is unsigned
    -- (`bv2nat`), `toInt` two's-complement signed (`sbv_to_int`); `ofInt` wraps.
    -- Both operators are supported by z3 and cvc5 (checked).
    | BitVec.toNat _ a => return some (.symbApp "bv2nat" #[← emitTerm a])
    | BitVec.toInt _ a => return some (.symbApp "sbv_to_int" #[← emitTerm a])
    | BitVec.ofInt width i =>
      let some wv ← natValue? width | return none
      return some (.app (.indexed "int2bv" #[.inr wv]) #[← emitTerm i])
    | _ => return none

  /-- A rotation. SMT-LIB encodes the amount as an identifier *index*
  (`((_ rotate_left k) x)`), so a symbolic amount cannot be expressed and is
  refused rather than mistranslated. -/
  partial def rotateOp (op : String) (a b : Expr) : TranslateM (Option SMT.Term) := do
    let some amt ← natValue? b | return none
    return some (.app (.indexed op #[.inr amt]) #[← emitTerm a])

  /-- A shift, coercing a `Nat` shift amount to a same-width bit-vector literal as
  SMT-LIB requires. A symbolic `Nat` amount cannot be coerced and is refused. -/
  partial def shiftOp (op : String) (w : Nat) (a b : Expr) : TranslateM (Option SMT.Term) := do
    let sa ← emitTerm a
    if let some bw ← bvWidthOf? b then
      -- Same-width bit-vector amount: pad if the widths differ.
      return some (.symbApp op #[sa, bvResize false bw w (← emitTerm b)])
    if (← whnf (← inferType b)).isConstOf ``Nat then
      let some bv ← natValue? b | return none
      -- Saturate at the width: both Lean and SMT yield 0 (or sign-fill) there, and
      -- the literal must fit in `w` bits to be representable.
      return some (.symbApp op #[sa, bvLit w (min bv w)])
    return none

  /-- String operations. `str.len` counts codepoints, matching `String.length`. -/
  partial def stringTerm? (e : Expr) : TranslateM (Option SMT.Term) := do
    match_expr e with
    | String.length s =>
      return some (.symbApp "str.len" #[← emitTerm s])
    | String.append a b =>
      return some (.symbApp "str.++" #[← emitTerm a, ← emitTerm b])
    | String.isPrefixOf a b =>
      return some (.symbApp "str.prefixof" #[← emitTerm a, ← emitTerm b])
    | HAppend.hAppend _ _ _ _ a b =>
      -- Only claim `++` when it really is string append.
      if (← isStringType (← inferType a)) then
        return some (.symbApp "str.++" #[← emitTerm a, ← emitTerm b])
      else return none
    | _ => return none

  /-- `p → q` where `p : Prop`.

  The domain must itself be a *proposition*. A non-dependent arrow whose domain is a
  `Type` — `Empty → False`, say — is a function type, not an implication: its SMT
  image is a function sort, and treating the domain as an antecedent emits a
  non-`Bool` argument to `=>`. Falls through to the quantifier path, which handles
  the uninhabited domain (there, correctly, by refusing). -/
  partial def tryImplication (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .forallE _ ty body _ =>
      if body.hasLooseBVar 0 then return none
      unless (← isProp ty) do return none
      return some (.symbApp "=>" #[← emitTerm ty, ← emitTerm body])
    | _ => return none

  /-- Translate `∀ (x : ty), body` / `∃ (x : ty), body` over a non-Prop sort.
  A fresh SMT-bound variable is introduced; a `Nat` domain gets a `≥ 0` guard.
  The SMT quantifier uses the *named* binder form (not de Bruijn), so we register
  the introduced fvar → name mapping and reference it directly. -/
  partial def quantifier (isForall : Bool) (ty body : Expr) : TranslateM (Option SMT.Term) := do
    -- SMT sorts are non-empty; a Lean quantifier over an uninhabited type is not
    -- faithfully representable (`∀ x : Empty, P` is vacuously true, its SMT image
    -- is not). Refuse rather than emit an unsound encoding.
    if ← isEmptyType ty then
      throwError "crush: cannot translate a quantifier over the uninhabited type \
                  `{ty}` — every SMT sort is non-empty, so the encoding would be \
                  unsound. Eliminate the quantifier first (e.g. `exact absurd .. ..`)."
    let sort ← emitSort ty
    let vname ← TranslateM.freshSymbol "q"
    -- Enter the binder with a real fvar so `body` becomes a closed Expr, and bind
    -- that fvar to the SMT variable name so occurrences render as `vname`.
    -- A *function-typed* domain additionally registers the variable as a `funVar`
    -- so its applications route through the arrow sort's `app` symbol; without
    -- this the body would declare a fresh function unrelated to the bound
    -- variable, which is unsound (it over-constrains the hypothesis).
    let inner ← withLocalDeclD (Name.mkSimple vname) ty fun x => do
      let k := emitTerm (body.instantiate1 x)
      if (← whnf ty).isArrow then
        -- In native mode the variable is applied directly, so no `app` symbol (and
        -- no `Fn` sort) is needed; `funVar?` still marks it as function-typed.
        let appSym ←
          if (← TranslateM.getConfig).hoMode == .native then pure vname
          else pure (← declareArrowSort ty).2
        TranslateM.withBoundVar x.fvarId! vname
          (TranslateM.withFunVar x.fvarId! appSym k)
      else
        TranslateM.withBoundVar x.fvarId! vname k
    let guarded ← guardSort isForall ty vname inner
    if isForall then
      return some (.forallE #[(vname, sort)] guarded)
    else
      return some (.existsE #[(vname, sort)] guarded)

  /-- Restrict a quantifier to the well-formed subset of its SMT sort.

  Needed whenever the Lean type embeds into a strictly larger SMT sort: `Nat` into
  `Int`, and any datatype with a `Nat` field into its freely-generated SMT datatype.
  `∀` becomes `wf x ⇒ body`, `∃` becomes `wf x ∧ body`. Without this the solver may
  reason about phantom values (negative `Nat`s) and derive `False` from true
  hypotheses. -/
  partial def guardSort (isForall : Bool) (ty : Expr) (vname : String) (body : SMT.Term) :
      TranslateM SMT.Term := do
    match ← wfCondition ty (.const vname) with
    | none => return body
    | some cond =>
      if isForall then return .symbApp "=>" #[cond, body]
      else return .symbApp "and" #[cond, body]

  /-- Uninterpreted-function fallback: declare the head, translate the args.

  If the head's result type is `Nat`, we additionally emit its non-negativity
  well-formedness constraint (`emitNatWF`) so the `Int` encoding cannot assign it
  a negative value — closing the soundness hole for `Nat`-valued atoms/functions
  (a bare `n : Nat` free variable, `f : α → Nat`, etc.). -/
  partial def defaultApp (fn : Expr) (args : Array Expr) : TranslateM SMT.Term := do
    -- Type and proof arguments carry no runtime content and have no SMT
    -- counterpart: `List.length Int []` is a function of the list alone. Passing
    -- them through would emit the *type* as a term — `Int` became a `Bool`-sorted
    -- constant fed to an `Int`-returning symbol — producing ill-sorted output.
    -- Note z3 does not reject that; it silently reinterprets, so nothing would
    -- surface at the boundary.
    let valueArgs ← args.filterM fun a => do
      let ty ← inferType a
      -- Drop the argument when it *is* a type (`α : Type`) or a proof (`h : p`).
      if (← isProp ty) then return false
      return !(← whnf ty).isSort
    -- The symbol is keyed on the head *together with its dropped arguments*, so
    -- distinct instantiations of a polymorphic constant get distinct symbols
    -- rather than being conflated into one ill-sorted declaration.
    let dropped := args.size - valueArgs.size
    let key ←
      if dropped == 0 then
        pure s!"{toString (← ppExpr fn)}"
      else
        let tyKeys ← args.filterMapM fun a => do
          let ty ← inferType a
          if (← isProp ty) then return none
          if (← whnf ty).isSort then return some (toString (← ppExpr a)) else return none
        pure s!"{toString (← ppExpr fn)}@{String.intercalate "," tyKeys.toList}"
    let hint ← headHint fn
    let name ← TranslateM.symbolFor key hint
    if !(← declaredFun name) then
      let argSorts ← valueArgs.mapM (fun a => do emitSort (← inferType a))
      let appExpr := mkAppN fn args
      let resTy ← whnf (← inferType appExpr)
      let resSort ← emitSort resTy
      TranslateM.emitCommand (.declFun name argSorts resSort)
      markFunDeclared name
      emitResultWF name argSorts resTy
    -- A *function-typed* argument must be passed as a value of its `Fn` sort, not
    -- as a first-order symbol: `emitSort` already gave the parameter an `Fn` sort,
    -- so emitting the bare symbol would be a sort mismatch. `emitFunValue`
    -- η-expands a named function into a closure.
    let sargs ← valueArgs.mapM fun a => do
      if ← isFunctionType (← inferType a) then emitFunValue a else emitTerm a
    return .app (.symb name) sargs

  /-- Constrain an uninterpreted symbol's *result* to the well-formed subset of its
  sort — the `Nat`-valued case (`f : α → Nat` is never negative) generalized to any
  guarded type. Nullary symbols get a bare assertion; higher arity a quantified one
  over fresh variables. Emitted once, at declaration time. -/
  partial def emitResultWF (name : String) (argSorts : Array SSort) (resTy : Expr) :
      TranslateM Unit := do
    if argSorts.isEmpty then
      if let some c ← wfCondition resTy (.const name) then
        TranslateM.emitCommand (.assert c)
      return
    let mut binders : Array (String × SSort) := #[]
    let mut appArgs : Array SMT.Term := #[]
    for s in argSorts do
      let v ← TranslateM.freshSymbol "w"
      binders := binders.push (v, s)
      appArgs := appArgs.push (.const v)
    if let some c ← wfCondition resTy (.app (.symb name) appArgs) then
      TranslateM.emitCommand (.assert (.forallE binders c))

  partial def headHint (fn : Expr) : TranslateM String := do
    match fn with
    | .const n _ => return nameHint n
    | .fvar fid => return nameHint (← fid.getUserName)
    | _ => return "f"
end

end Crush
