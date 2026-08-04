import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Theories
open Lean Meta

/-!
# The translation driver: `Expr → SMT.Term`

Lowers a (monomorphic, first-order-after-encoding) Lean `Expr` into an
`SMT.Term`, dispatching to user `@[crush_translate]` handlers before the default
structural translator. This is the piece that constructs the `TranslationCtx`
closures (`emitTerm`/`emitSort`/`declare`) handlers recurse through.

Milestone-1 scope: propositional/Boolean structure, equality, quantifiers over a
declared sort, `Int`/`Nat` (Nat via Int with a `≥ 0` guard on quantifiers), and
uninterpreted functions/atoms. Bit-vectors, strings, datatypes, and the HO
encoding land in later milestones; anything unrecognized becomes a fresh
uninterpreted symbol so translation degrades rather than crashing.
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

/-- A supported (non-parametric, non-indexed, `Type`-valued) inductive we can emit
as an SMT datatype: enumerations, simple structures, and — since `declare-datatypes`
is itself recursive — self-recursive types such as `List`-like or tree shapes.

We still require at least one constructor: SMT-LIB datatypes must be inhabited
(z3 rejects `(declare-datatypes ((E 0)) (()))`), and more fundamentally every SMT
sort is non-empty while `Empty` is not, so an empty Lean inductive cannot be
modelled faithfully and must stay an opaque sort. See `emptyTypeBail`. -/
def isSupportedDatatype (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | return false
  if iv.numParams != 0 || iv.numIndices != 0 then return false
  if n == ``Nat || n == ``Int || n == ``Bool || n == ``String then return false
  if iv.ctors.isEmpty then return false
  unless iv.type.getForallBody.isType do return false
  -- Every constructor field must itself be translatable to a sort. A field whose
  -- type mentions the datatype only in a *strictly positive, direct* way (`T`
  -- itself) is fine; a field of function type into `T` is not, and would need the
  -- HO encoding (Milestone 3).
  iv.ctors.allM fun ctorName => do
    let ci ← getConstInfoCtor ctorName
    forallTelescopeReducing ci.type fun args _ =>
      args.allM fun a => do
        let ty ← whnf (← inferType a)
        -- Reject fields that are proofs/dependent or arrow-typed mentioning `n`.
        if ty.isForall then
          return !(ty.getForallBody.isAppOf n) && !ty.getForallBody.isConstOf n
        return true

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
  nullary uninterpreted sort keyed by the type's canonical form. -/
  partial def emitSort (e : Expr) : TranslateM SSort := do
    let e ← whnf e
    match e with
    | .const ``Bool _ => return .app (.symb "Bool") #[]
    | .const ``Nat _  => return .app (.symb "Int") #[]
    | .const ``Int _  => return .app (.symb "Int") #[]
    | .const ``String _ => return .app (.symb "String") #[]
    | .sort _         => return .app (.symb "Bool") #[]  -- Prop / Sort ↦ Bool
    | _ =>
    -- `BitVec w` at a statically-known width maps to the indexed sort
    -- `(_ BitVec w)`. A symbolic width has no SMT counterpart, so it falls through
    -- to an opaque sort (where `BitVec` ops will not be recognized either).
    match ← bvWidthOfType? e with
    | some w => return bvSort w
    | none =>
    match e with
    | .const n _ =>
      if ← isSupportedDatatype n then
        return .app (.symb (← declareDatatype n)) #[]
      else
        declareUninterpretedSort e
    | _ => declareUninterpretedSort e

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
  partial def declareDatatype (n : Name) : TranslateM String := do
    let key := s!"__datatype__{n}"
    if let some name := (← get).atomToName.get? key then
      return name
    let sortName ← TranslateM.symbolFor key (nameHint n)
    -- Register the sort name *before* translating field sorts: a recursive
    -- datatype's fields mention the type itself, and must resolve to this symbol
    -- rather than recursing forever.
    markSortDeclared sortName
    let iv ← getConstInfoInduct n
    let mut ctorDecls : Array CtorDecl := #[]
    -- Field descriptors for the wf axiom: per ctor, the selectors needing a guard.
    let mut wfParts : Array (String × Array (String × Expr)) := #[]
    for ctorName in iv.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let (selDecls, guards) ← forallTelescopeReducing ctorInfo.type fun args _ => do
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
    let .const n _ := ty.getAppFn | return false
    if !(← isSupportedDatatype n) then return false
    -- Guard against cycles: a recursive datatype needs a guard iff some field does,
    -- and self-reference alone contributes nothing new.
    let iv ← getConstInfoInduct n
    iv.ctors.anyM fun ctorName => do
      let ci ← getConstInfoCtor ctorName
      forallTelescopeReducing ci.type fun args _ =>
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
    let .const n _ := ty.getAppFn | return none
    if !(← isSupportedDatatype n) then return none
    if !(← needsWFGuard ty) then return none
    let sortName ← declareDatatype n
    return some (.app (.symb (wfSymbol sortName)) #[t])

  /-- Translate a term, trying user handlers first. -/
  partial def emitTerm (e : Expr) : TranslateM SMT.Term := do
    let e ← instantiateMVars e
    -- A quantifier-bound variable renders as its SMT name, never a declaration.
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- Fast path for the structural logical/theory core.
    match ← structural? e with
    | some t => return t
    | none =>
      -- Try user handlers on the applied head.
      let (fn, args) := getAppFnArgs' e
      let ctx : TranslationCtx := {
        fn, args
        emitTerm := emitTerm
        emitSort := emitSort
        declare  := declareViaThunk }
      for h in (← getTranslationHandlers) do
        if let some t ← h ctx then
          return t
      -- A constructor of a supported datatype → the SMT constructor symbol.
      if let some t ← ctorApp? fn args then
        return t
      -- A structure projection → the SMT selector.
      if let some t ← projApp? fn args then
        return t
      -- Default: uninterpreted function/atom applied to translated args.
      defaultApp fn args

  /-- If `fn` is a projection of a supported single-constructor datatype, translate
  `fn s` to the SMT selector `<ctor>_sel<i> s`. -/
  partial def projApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const pn _ := fn | return none
    let some info ← getProjectionFnInfo? pn | return none
    if !(← isSupportedDatatype info.ctorName.getPrefix) then return none
    -- Projections take the structure as the argument after `info.numParams`.
    let some structArg := args[info.numParams]? | return none
    let sortName ← declareDatatype info.ctorName.getPrefix
    let sel := selSymbol sortName info.ctorName info.i
    let extraArgs := args.extract (info.numParams + 1) args.size
    let sarg ← emitTerm structArg
    let sextra ← extraArgs.mapM emitTerm
    return some (.app (.symb sel) (#[sarg] ++ sextra))

  /-- If `fn` is a constructor of a supported datatype, translate the application
  to the corresponding SMT constructor symbol applied to the translated args
  (ensuring the datatype is declared first). -/
  partial def ctorApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const cn _ := fn | return none
    let env ← getEnv
    let some (.ctorInfo ci) := env.find? cn | return none
    if !(← isSupportedDatatype ci.induct) then return none
    let sortName ← declareDatatype ci.induct
    let sargs ← args.mapM emitTerm
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
          -- `p → q` as a Prop implication.
          let a ← emitTerm ty
          let b ← emitTermUnderNothing body
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
      let some nv ← natValue? n | return none
      return some (bvLit wv nv)
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
    | _ => return none

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

  /-- `p → q` where `p : Prop`. -/
  partial def tryImplication (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .forallE _ ty body _ =>
      if body.hasLooseBVar 0 then return none
      return some (.symbApp "=>" #[← emitTerm ty, ← emitTerm body])
    | _ => return none

  /-- Body of a non-dependent Prop implication translated without introducing a
  binder (the bound variable does not occur). -/
  partial def emitTermUnderNothing (body : Expr) : TranslateM SMT.Term := do
    emitTerm body

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
    let inner ← withLocalDeclD (Name.mkSimple vname) ty fun x => do
      TranslateM.withBoundVar x.fvarId! vname (emitTerm (body.instantiate1 x))
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
    let key := toString (← ppExpr fn)
    let hint ← headHint fn
    let name ← TranslateM.symbolFor key hint
    if !(← declaredFun name) then
      let argSorts ← args.mapM (fun a => do emitSort (← inferType a))
      let appExpr := mkAppN fn args
      let resTy ← whnf (← inferType appExpr)
      let resSort ← emitSort resTy
      TranslateM.emitCommand (.declFun name argSorts resSort)
      markFunDeclared name
      emitResultWF name argSorts resTy
    let sargs ← args.mapM emitTerm
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
