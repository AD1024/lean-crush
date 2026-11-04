import Lean
import Crush.SMT.Syntax
import Crush.SMT.Quote
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Theories
import Crush.Translation.HOEncoding

/-!
# The translation driver: `Expr → SMT.Term`

Translate Lean expressions through general handlers, targeted lowerings, and the
structural logical, theory, datatype, and higher-order encodings. Unsupported
operations remain uninterpreted only when their signatures can be represented safely.

Potentially empty carriers use padding and validity guards. Built-in sort keys cannot
capture translated binders, erased arguments cannot hide value dependencies, and
encoding decisions retain their evidence. Higher-order application stays connected
to function values; native lambdas agree on a canonical extension outside valid inputs.

The mutually recursive metaprograms are partial because type inference and definitional
reduction can expose syntax larger than their input. Under trusting discharge,
translation and solver semantics are trusted; reconstruction requires a checked Lean
proof. Local comments describe the guards needed at each encoding boundary.
-/

open Lean Meta

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
    unless ← hasExpectedOfNatInstance e do return none
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

/-- Compare a structural operator with the fixed library dictionary it models.
Global and local overrides must both remain uninterpreted. -/
def hasCanonicalInstance (e : Expr) (i : Nat) : TranslateM Bool :=
  hasExpectedOverloadInstance e i

/-- Whether `inst` is accompanied by a `LawfulBEq` proof for `carrier`.

Unlike arithmetic dictionaries, a nonstandard `BEq` can still be translated as
SMT equality when the local context proves that it coincides with propositional
equality. Without this check, `⟨fun _ _ => false⟩ : BEq α` would make `a == a`
translate to the true SMT equation `a = a`. -/
def hasLawfulBEq (carrier inst : Expr) : TranslateM Bool := do
  let carrier ← instantiateMVars carrier
  let some level := (← getLevel carrier).dec | return false
  try
    let expected := mkApp2 (mkConst ``LawfulBEq [level]) carrier inst
    let proof ← (show MetaM Expr from withoutModifyingState <| withNewMCtxDepth do
      instantiateMVars (← synthInstance expected))
    TranslateM.recordEncodingEvidence expected proof
  catch _ =>
    return false

/-- SMT datatypes require a finite constructor tree for every mutually declared sort.
A Lean inductive may have only recursive constructors and therefore be empty. Keep
such a block opaque and guarded instead of emitting an invalid SMT datatype. -/
private def hasProductiveDatatypeBlock (iv : InductiveVal) : MetaM Bool := do
  let block := iv.all.toArray
  let mut productive : Std.HashSet Name := {}
  for _ in [:block.size] do
    for name in block do
      if productive.contains name then continue
      let info ← getConstInfoInduct name
      for ctor in info.ctors do
        let ctorInfo ← getConstInfoCtor ctor
        -- Inspect fields before parameter substitution: a nested product parameter is
        -- an external padded sort, whose Lean validity is checked by datatype guards.
        let ready ← forallTelescopeReducing ctorInfo.type fun binders _ =>
          (binders.extract ctorInfo.numParams binders.size).allM fun field => do
            let ty ← whnf (← inferType field)
            let .const head _ := ty.getAppFn | return true
            return !block.contains head || productive.contains head
        if ready then
          productive := productive.insert name
          break
  return block.all productive.contains

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
  unless ← hasProductiveDatatypeBlock iv do return false
  -- Keep classes opaque so custom instance dictionaries are never assigned
  -- SMT datatype semantics.
  if isClass env n then return false
  -- Datatype parameters must be ground types: List Int can be structural,
  -- while List α with an unresolved or free parameter remains opaque.
  for a in typeArgs do
    let aty ← whnf (← inferType a)
    unless aty.isSort do return false
    if (← instantiateMVars a).hasExprMVar then return false
  -- Exclude Prop while permitting universe-polymorphic sorts such as PUnit.
  unless (match iv.type.getForallBody with
          | .sort l => !l.isZero
          | _ => false) do
    return false
  -- Instantiated fields must be data with non-function SMT sorts. Direct
  -- positive recursion is supported; proof and function fields remain opaque.
  let fieldsOk ← iv.ctors.allM fun ctorName => do
    let ci ← getConstInfoCtor ctorName
    let ctorTy ← instantiateForall ci.type typeArgs
    forallTelescopeReducing ctorTy fun args _ =>
      args.allM fun a => do
        let ty ← whnf (← inferType a)
        if ty.isForall then return false
        if ← isProp ty then return false
        return true
  unless fieldsOk do return false
  -- Emit only Lean's own mutual block. Recursion through an external datatype
  -- would require a larger SMT declaration block and otherwise forward-reference
  -- an undeclared sort; keep such types opaque.
  return !(← escapesBlock n iv.all.toArray typeArgs)
where
  /-- Whether some constructor field reaches back into `block` through a datatype *outside*
  `block`. `block` is `n`'s Lean mutual block, which is emitted as a unit. -/
  escapesBlock (n : Name) (block : Array Name) (typeArgs : Array Expr) : MetaM Bool := do
    let inBlock : Std.HashSet Name := block.foldl (·.insert ·) {}
    let some (.inductInfo iv) := (← getEnv).find? n | return false
    iv.ctors.anyM fun ctorName => do
      let ci ← getConstInfoCtor ctorName
      let ctorTy ← instantiateForall ci.type typeArgs
      forallTelescopeReducing ctorTy fun args _ =>
        args.anyM fun a => do
          let fty ← whnf (← inferType a)
          -- Members of this mutual block are emitted together; do not follow that recursion.
          match fty.getAppFn with
          | .const m _ => if inBlock.contains m then return false
          | _ => pure ()
          reaches inBlock fty 8 inBlock

  /-- Whether `ty`'s constructor-field closure mentions any member of `targets`. -/
  reaches (targets : Std.HashSet Name) (ty : Expr) (fuel : Nat)
      (visiting : Std.HashSet Name) : MetaM Bool := do
    match fuel with
    | 0 => return false
    | fuel + 1 =>
      let ty ← whnf ty
      let .const m _ := ty.getAppFn | return false
      if targets.contains m then return true
      if visiting.contains m then return false
      let some (.inductInfo miv) := (← getEnv).find? m | return false
      if miv.numIndices != 0 then return false
      let margs := ty.getAppArgs
      if margs.size != miv.numParams then return false
      let visiting := visiting.insert m
      miv.ctors.anyM fun c => do
        let ci ← getConstInfoCtor c
        let some cty ← (try pure (some (← instantiateForall ci.type margs))
                        catch _ => pure none) | pure false
        forallTelescopeReducing cty fun args _ =>
          args.anyM fun a => do reaches targets (← inferType a) fuel visiting

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

/-- Check that an opaque carrier is inhabited in the original query context.

SMT sorts are nonempty even when used only in generated closure equations or
datatype fields. Checking source quantifiers alone is therefore insufficient.
An actual local value or a `Nonempty` instance justifies an unguarded carrier;
otherwise its SMT sort needs a predicate restricting it to Lean inhabitants.

Do not consult translation's extended local context: a hypothetical field
`x : Empty` introduced while inspecting `Option Empty` is not a witness. -/
private def knownNonemptyCarrier (ty : Expr) : TranslateM Bool := do
  let ty ← instantiateMVars ty
  let st ← get
  if let some result := st.nonemptyCarriers[ty]? then return result
  let expected ← mkAppM ``Nonempty #[ty]
  let evidence? ← (show MetaM (Option Expr) from withLCtx st.inputLCtx st.inputLocalInstances do
    withoutModifyingState <| withNewMCtxDepth do
      for decl in st.inputLCtx do
        if decl.isImplementationDetail then continue
        if ← isDefEqGuarded decl.type ty then
          return some (← instantiateMVars (← mkAppM ``Nonempty.intro #[decl.toExpr]))
        let prop ← whnf decl.type
        if prop.isAppOfArity ``Nonempty 1 then
          if ← isDefEqGuarded prop.appArg! ty then return some decl.toExpr
      try
        return some (← instantiateMVars (← synthInstance expected))
      catch _ => return none)
  let nonempty ← match evidence? with
    | some evidence => TranslateM.recordEncodingEvidence expected evidence
    | none => pure false
  modify fun s => { s with nonemptyCarriers := s.nonemptyCarriers.insert ty nonempty }
  return nonempty

/-- An inhabited defunctionalized arrow needs no padding functions: its
uninterpreted `Fn` sort can consist entirely of Lean functions. Besides ordinary
inhabitation evidence, a nonempty result supplies a constant function, and a
result matching an argument supplies a projection (including `α → α`, even when
`α` may be empty).

Native SMT function sorts contain all functions on the padded SMT carriers, so
they must retain their validity predicates even when the Lean arrow is inhabited. -/
private def knownNonemptyDefunctionalizedArrow (ty : Expr) (shape : ArrowShape) :
    TranslateM Bool := do
  if (← TranslateM.getConfig).hoMode == .native then return false
  if ← shape.args.anyM (isDefEqRigid · shape.res) then return true
  if ← knownNonemptyCarrier shape.res then return true
  return ← knownNonemptyCarrier ty

/-- Whether `e` is a *value* that a type could depend on: something crush turns
into an SMT term, such as a number, a Boolean, a proposition or a predicate.
Types and type constructors (`Int`, `List`) are not values. Neither are proofs,
which crush erases, nor type-class instances, which Lean fills in automatically. -/
def isValueForDependency (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  if ← isProp ty then return false
  forallTelescopeReducing ty fun _ result => do
    match ← whnf result with
    | .sort level => return level.isZero
    | result => return (← isClass? result).isNone

/-- Whether `ty` is a dependent type, which crush has no sound way to translate.
Two shapes count:

* a function type whose result type depends on its argument, such as
  `(n : Nat) → β n`;
* a type that takes or mentions a value, such as `Fin n`, `BitVec k`, `β 0` or
  `Vector α n`.

Types built only from other types, such as `List α` or `Int → Bool`, do not
count, and neither do propositions. -/
def isDependentType (ty : Expr) : MetaM Bool := do
  if ← isProp ty then return false
  let ty ← whnf ty
  if ty.isForall then return !ty.isArrow
  if ← ty.getAppArgs.anyM isValueForDependency then return true
  (Lean.collectFVars {} ty).fvarIds.anyM fun id => isValueForDependency (.fvar id)

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

/-- Allocate the constructor symbol identified by its datatype and Lean declaration. -/
def reserveCtorSymbol (sortName : String) (ctorName : Name) : TranslateM String :=
  TranslateM.reserveDerivedFor {
    tag := "datatype-constructor"
    parent := sortName
    member := ctorName
  } (ctorSymbol sortName ctorName)

/-- Allocate the selector symbol identified by its datatype, constructor, and field. -/
def reserveSelSymbol (sortName : String) (ctorName : Name) (i : Nat) : TranslateM String :=
  TranslateM.reserveDerivedFor {
    tag := "datatype-selector"
    parent := sortName
    member := ctorName
    index := some i
  } (selSymbol sortName ctorName i)

/-- The SMT tester `((_ is C) x)`. -/
def testerApp (ctorSym : String) (x : SMT.Term) : SMT.Term :=
  .app (.indexed "is" #[.inl ctorSym]) #[x]

/-- The well-formedness predicate symbol for a datatype sort. -/
def wfSymbol (sortName : String) : String := s!"wf_{sortName}"

/-- Allocate the well-formedness predicate associated with a datatype sort. -/
def reserveWfSymbol (sortName : String) : TranslateM String :=
  TranslateM.reserveDerivedFor {
    tag := "datatype-well-formedness"
    parent := sortName
  } (wfSymbol sortName)

/-- Symbols allocated for Crush's finite representation of `Array elem`. The
total SMT array is paired with a logical length; selectors and the out-of-range
sentinel are qualified by the structurally allocated sort name. Exposed to
lowering handlers through `withFiniteArray`. -/
structure FiniteArrayEncoding where
  sortName : String
  ctor     : String
  lenSel   : String
  dataSel  : String
  sentinel : String

private def finiteArrayEncodingNames (sortName sentinel : String) :
    TranslateM FiniteArrayEncoding := do
  return {
    sortName
    ctor := ← TranslateM.reserveDerivedFor {
      tag := "finite-array-constructor"
      parent := sortName
    } s!"{sortName}_mk"
    lenSel := ← TranslateM.reserveDerivedFor {
      tag := "finite-array-length-selector"
      parent := sortName
    } s!"{sortName}_len"
    dataSel := ← TranslateM.reserveDerivedFor {
      tag := "finite-array-data-selector"
      parent := sortName
    } s!"{sortName}_data"
    sentinel
  }

/-- Whether a declaration's result is intrinsically logical, before substituting
its polymorphic parameters. This distinction keeps a data projection such as
`GetElem.getElem` out of the logical reduction path even when instantiated at
`Bool`. -/
private partial def hasDeclaredLogicalCodomain : Expr → Bool
  | .forallE _ _ body _ => hasDeclaredLogicalCodomain body
  | .sort .zero => true
  | body => body.isConstOf ``Bool

/-- Whether `fn` is a class field whose declared result is `Prop` or `Bool`. -/
private def isLogicalClassProjection (fn : Expr) : MetaM Bool := do
  let .const head _ := fn | return false
  let some info ← getProjectionFnInfo? head | return false
  unless info.fromClass do return false
  let some decl := (← getEnv).find? head | return false
  return hasDeclaredLogicalCodomain decl.type

/-- Dispatch head for a result-indexed lowering. An immediate type head wins;
otherwise dependent function binders are opened to expose a codomain such as
`Decidable (x = y)`. Named aliases therefore remain distinct dispatch keys. -/
private def resultHead? (ty : Expr) : MetaM (Option Name) := do
  let direct := ty.getAppFn
  if let .const head _ := direct then
    return some head
  forallTelescopeReducing ty fun _ body => do
    let body ← whnf body
    let .const head _ := body.getAppFn | return none
    return some head

private def finiteArraySentinelKey (elem : Expr) : StructuralKey := {
  tag := "finite-array-sentinel", name := ``Array, typeExprs := #[elem]
}

/-- Element type of a fully applied Lean `Array`, after reducible aliases. -/
def finiteArrayElem? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  let .const n _ := ty.getAppFn | return none
  if n != ``Array then return none
  let #[elem] := ty.getAppArgs | return none
  return some elem

/-- Whether `e` is an application of an overloaded arithmetic/comparison operator
whose instance argument is **not** the canonical global instance.

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

/-- The carrier type parameters of an overloaded operation that the structural
translator maps to the SMT integer theory.

Keeping this list in one place is deliberate: recognizing an operator head and a
canonical instance is not enough to select a theory. A canonical `LT α` for an
opaque `α`, for example, is still an uninterpreted relation rather than SMT's
integer `<`. -/
def integerOverloadCarriers? (e : Expr) : Option (Array Expr) :=
  match e.getAppFn with
  | .const fname _ =>
    let args := e.getAppArgs
    if fname == ``HAdd.hAdd || fname == ``HMul.hMul || fname == ``HSub.hSub
        || fname == ``HDiv.hDiv || fname == ``HMod.hMod then
      if args.size >= 3 then some (args.extract 0 3) else none
    else if fname == ``LE.le || fname == ``LT.lt || fname == ``GE.ge
        || fname == ``GT.gt || fname == ``Neg.neg || fname == ``Max.max
        || fname == ``Min.min then
      match args[0]? with
      | some carrier => some #[carrier]
      | none => none
    else
      none
  | _ => none

/-- Whether every carrier in an overloaded operation is the same supported SMT
integer carrier (`Nat` or `Int`).

Heterogeneous classes expose three carrier parameters. Requiring all three to
agree prevents a canonical mixed-carrier instance from being silently encoded as
ordinary integer arithmetic without an explicit coercion semantics. -/
def isHomogeneousIntegerCarrier (carriers : Array Expr) : TranslateM Bool := do
  let some first := carriers[0]? | return false
  let first ← whnf first
  unless first.isConstOf ``Nat || first.isConstOf ``Int do return false
  let firstIsNat := first.isConstOf ``Nat
  for carrier in carriers.extract 1 carriers.size do
    let carrier ← whnf carrier
    unless (if firstIsNat then carrier.isConstOf ``Nat else carrier.isConstOf ``Int) do
      return false
  return true

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

/-- A translated finite Array operand. `value` is a let-bound reference, so a
lowering may use `length` and `data` repeatedly without duplicating a nested
Array expression in the emitted SMT term. -/
structure FiniteArrayView where
  encoding : FiniteArrayEncoding
  value    : SMT.Term
  length   : SMT.Term
  data     : SMT.Term

/-- Construct a finite Array value from a logical length and SMT theory array. -/
def FiniteArrayView.mkValue (view : FiniteArrayView)
    (length data : SMT.Term) : SMT.Term :=
  .app (.symb view.encoding.ctor) #[length, data]

/-- Run a lowering over Crush's built-in finite representation of `arrayTy`.

Unlike `withFiniteArray`, this helper does not require an existing Array value.
It is intended for constructors such as `Array.replicate`. Returns `none` when
a user sort handler selected a different representation for the Array type.
-/
def withFiniteArrayType (ctx : TranslationCtx) (arrayTy elem : Expr)
    (k : FiniteArrayEncoding → TranslateM SMT.Term) :
    TranslateM (Option SMT.Term) := do
  let actualSort ← ctx.emitSort arrayTy
  let key : StructuralKey := {
    tag := "finite-array", name := ``Array, typeExprs := #[elem]
  }
  let some sortName ← TranslateM.structuralSymbol? key | return none
  unless actualSort == SSort.app (.symb sortName) #[] do return none
  let some sentinel ← TranslateM.structuralSymbol? (finiteArraySentinelKey elem)
    | throwError "internal error: finite Array sort `{sortName}` has no sentinel"
  let encoding ← finiteArrayEncodingNames sortName sentinel
  return some (← k encoding)

/-- Run a lowering over Crush's built-in finite representation of `arr`.

Returns `none` when a user `@[crush_translate_sort]` handler selected a different
representation, allowing the caller to defer to another lowering or the ordinary
uninterpreted fallback. The callback result is wrapped in an SMT `let`, so nested
updates remain linear in the source expression size.
-/
def withFiniteArray (ctx : TranslationCtx) (elem arr : Expr)
    (k : FiniteArrayView → TranslateM SMT.Term) :
    TranslateM (Option SMT.Term) := do
  let arrayTy ← inferType arr
  withFiniteArrayType ctx arrayTy elem fun encoding => do
    let arrayValue ← ctx.emitTerm arr
    let arrayName ← TranslateM.freshSymbol "array"
    let value := SMT.Term.const arrayName
    let view : FiniteArrayView := {
      encoding
      value
      length := SMT.Term.app (.symb encoding.lenSel) #[value]
      data := SMT.Term.app (.symb encoding.dataSel) #[value]
    }
    return .letE #[(arrayName, arrayValue)] (← k view)

private structure DefaultAppArgs where
  values    : Array Expr := #[]
  valuePositions : Array Nat := #[]
  types     : Array Expr := #[]
  instances : Array Expr := #[]

/-- Types and type constructors are erased signature parameters. Predicates
and proposition-valued functions remain values, represented with SMT Bool. -/
private def isTypeArgument (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ result => do
    let result ← whnf result
    return result.isSort && !result.isProp

/-- Partition application arguments by their Lean binder role.

Type and proof arguments are erased. Instance-implicit arguments affect the selected
Lean function but are encoded in its structural symbol rather than as opaque SMT values.
Explicit class-valued arguments remain ordinary values. -/
private def partitionDefaultAppArgs (fn : Expr) (args : Array Expr) :
    TranslateM DefaultAppArgs := do
  let mut applied := fn
  let mut fnType ← inferType fn
  let mut out : DefaultAppArgs := {}
  let boundVars := (← get).boundVars
  for index in [:args.size] do
    let arg := args[index]!
    let fnTypeWhnf ← whnf fnType
    let binderInfo? :=
      match fnTypeWhnf with
      | .forallE _ _ _ binderInfo => some binderInfo
      | _ => none
    let argType ← inferType arg
    if ← isProp argType then
      pure ()
    else if ← isTypeArgument argType then
      out := { out with types := out.types.push arg }
    else if binderInfo? == some .instImplicit then
      let dependsOnBound :=
        (Lean.collectFVars {} arg).fvarIds.any boundVars.contains
      if dependsOnBound then
        out := { out with values := out.values.push arg
                          valuePositions := out.valuePositions.push index }
      else
        out := { out with instances := out.instances.push arg }
    else
      out := { out with values := out.values.push arg
                        valuePositions := out.valuePositions.push index }
    applied := mkApp applied arg
    fnType ←
      match fnTypeWhnf with
      | .forallE _ _ body _ => pure (body.instantiate1 arg)
      | _ => inferType applied
  return out

/-- Replay takes only SMT value arguments. Keep the erased types, instances, and
proofs in the recorded function instead of asking the decoder to infer them again. -/
private def defaultReplayHead (fn : Expr) (args : Array Expr)
    (positions : Array Nat) : MetaM Expr := do
  if positions.size == args.size then return fn
  go positions.toList args #[]
where
  go (positions : List Nat) (args : Array Expr) (locals : Array Expr) : MetaM Expr := do
    match positions with
    | [] => mkLambdaFVars locals (mkAppN fn args)
    | position :: rest =>
      withLocalDeclD `arg (← inferType args[position]!) fun arg =>
        go rest (args.set! position arg) (locals.push arg)

/-- Built-in SMT sorts are fixed across quantifier and lambda instantiations.
Even a type binder must not occur in a sort key: type equality can distinguish
empty and inhabited instantiations of the same quantified type variable. -/
private def checkSortClosed (ty : Expr) : TranslateM Unit := do
  let st ← get
  if (Lean.collectFVars {} ty).fvarIds.any
      (fun id => st.boundVars.contains id || st.funVars.contains id) then
    throwError "crush: cannot translate a sort depending on a bound variable:{indentExpr ty}"

mutual
  /-- Sort translation. Interpreted Lean types map to SMT theory sorts; supported
  inductives are declared as SMT datatypes; everything else becomes a declared
  nullary uninterpreted sort keyed by the type's canonical form.

  User `@[crush_translate_sort]` handlers get first refusal (like term handlers in
  `emitTerm`), so a user can retarget a Lean type to a theory sort — e.g. a finite map
  to SMT's `(Array K V)`. Skipped wholesale when none are registered.

  Handlers see the type *before* weak-head normalization, so one registered for a type
  introduced by `def`/`abbrev` still fires; they are offered the normalized form
  afterwards, for a handler registered against that instead. -/
  partial def emitSort (e : Expr) : TranslateM SSort := do
    let e ← instantiateMVars e
    let handlers ← if ← hasSortHandlers then getSortHandlers else pure #[]
    if let some s ← trySortHandlers handlers e then return s
    let normalized ← whnf e
    if normalized != e then
      if let some s ← trySortHandlers handlers normalized then return s
    let e := normalized
    checkSortClosed e
    match e with
    | .const ``Bool _ => return .app (.symb "Bool") #[]
    | .const ``Nat _  => return .app (.symb "Int") #[]
    | .const ``Int _  => return .app (.symb "Int") #[]
    | .const ``String _ => return .app (.symb "String") #[]
    -- Only Prop maps to Bool. Collapsing higher universes to two values would
    -- identify distinct Lean types; represent those universes by opaque sorts.
    | .sort l => if l.isZero then return .app (.symb "Bool") #[]
                 else declareUninterpretedSort e
    | _ =>
    -- Encode finite arrays by a length and a theory array for native read/write semantics.
    if let some elem ← finiteArrayElem? e then
      let enc ← declareFiniteArray elem
      return .app (.symb enc.sortName) #[]
    -- Literal widths use indexed SMT bit-vector sorts; symbolic widths are refused below.
    match ← bvWidthOfType? e with
    | some w => return bvSort w
    | none =>
    -- Function values need an arrow encoding that keeps applications linked to the value.
    if (← whnf e).isArrow then
      if (← TranslateM.getConfig).hoMode == .native then
        let some shape ← arrowShape? e
          | throwError "crush: internal — non-arrow in arrow branch: {e}"
        return nativeArrowSort (← shape.args.mapM emitSort) (← emitSort shape.res)
      let (sort, _) ← declareArrowSort e
      return sort
    -- Supported inductives receive distinct SMT datatypes for each type instantiation.
    match ← supportedDatatypeType? e with
    | some (n, typeArgs) =>
      let name ← declareDatatype n typeArgs (some e)
      return .app (.symb name) #[]
    | none =>
      -- An opaque sort cannot vary with a value binder, and dependent function
      -- applications cannot use a fixed arrow signature. Refuse unsupported dependent
      -- types, including fixed instances such as Fin 5; earlier handlers may encode them.
      if ← isDependentType e then
        throwError "crush: cannot translate the dependent type{indentExpr e}\n\
                    A dependent type is a type that depends on a value, such as \
                    `Fin n`, or a function type whose result type depends on its \
                    argument, such as `(n : Nat) → β n`. crush cannot translate \
                    these types to SMT without risking false proofs. Restate the \
                    goal without this type, or prove it another way."
      declareUninterpretedSort e

  /-- Declare the `Fn` sort and `app` symbol for an arrow type `σ₁ → … → τ`, once.
  Returns the sort and its `app` symbol name.

  The `app` symbol is *n*-ary over the flattened argument list rather than a chain
  of unary applies: `Int → Int → Bool` gets `app (Fn Int Int) Int → Bool` in one
  step. This keeps the encoding small for the common fully-applied case. Partial
  application is handled separately (`partialApp?`) by materializing the
  intermediate closure.

  The `app` result carries the codomain's well-formedness constraint at well-formed
  arguments — the arrow-sort counterpart of `emitResultWF`, confining `app f n` for a
  `Nat`-codomain arrow to the nonnegative `Int`s. -/
  partial def declareArrowSort (ty : Expr) : TranslateM (SSort × String) := do
    let ty ← instantiateMVars ty
    checkSortClosed ty
    let some shape ← arrowShape? ty
      | throwError "crush: internal — `declareArrowSort` on a non-arrow {ty}"
    let key := arrowKey ty
    let sortName ← TranslateM.symbolForStructural key "Fn"
    let sort := SSort.app (.symb sortName) #[]
    let aKey := appKey ty
    let appName ← TranslateM.symbolForStructural aKey s!"app_{sortName}"
    TranslateM.recordSymbolExpr sortName ty
    let appHead ← withLocalDeclD `fn ty fun fn => mkLambdaFVars #[fn] fn
    TranslateM.recordSymbolExpr appName appHead
    if !(← declaredSort sortName) then
      markSortDeclared sortName
      TranslateM.emitCommand (.declSort sortName 0)
      let argSorts ← shape.args.mapM emitSort
      let resSort ← emitSort shape.res
      TranslateM.emitCommand (.declFun appName (#[sort] ++ argSorts) resSort)
      markFunDeclared appName
      let fName ← TranslateM.freshSymbol "wf_f"
      let mut names : Array String := #[]
      for _ in shape.args do
        names := names.push (← TranslateM.freshSymbol "wf_x")
      let appTerm := SMT.Term.app (.symb appName)
        (#[SMT.Term.const fName] ++ names.map (SMT.Term.const ·))
      if let some res ← wfCondition shape.res appTerm then
        let guarded ←
          match ← binderGuard names shape.args with
          | none => pure res
          | some g => pure (smt| (=> $g $res))
        if ← knownNonemptyDefunctionalizedArrow ty shape then
          -- This sort can contain only actual functions. Constrain application
          -- globally, retaining argument guards when the domain itself is padded.
          TranslateM.emitCommand (.assert
            (.forallE (#[(fName, sort)] ++ names.zip argSorts) guarded))
        else
          let wf ← reserveWfSymbol sortName
          markFunDeclared wf
          TranslateM.emitCommand (.defFun false wf #[(fName, sort)]
            (.app (.symb "Bool") #[]) (.forallE (names.zip argSorts) guarded))
          recordValidityPredicate wf ty
    return (sort, appName)

  /-- Offer a Lean type to `handlers`, in the priority order they were resolved in. -/
  partial def trySortHandlers (handlers : Array SortHandler) (e : Expr) :
      TranslateM (Option SSort) := do
    if handlers.isEmpty then return none
    let (fn, args) := getAppFnArgs' e
    let ctx : TranslationCtx := {
      fn, args
      emitTerm := emitTerm
      emitSort := emitSort
      declare  := declareViaThunk }
    for h in handlers do
      if let some s ← h ctx then
        return some s
    return none

  /-- The conjoined well-formedness conditions on SMT binders `names` of Lean types
  `tys`, or `none` when none of them constrains its sort. -/
  partial def binderGuard (names : Array String) (tys : Array Expr) :
      TranslateM (Option SMT.Term) := do
    let mut conds : Array SMT.Term := #[]
    for (n, ty) in names.zip tys do
      if let some c ← wfCondition ty (.const n) then
        conds := conds.push c
    if conds.isEmpty then return none
    if conds.size == 1 then return some conds[0]!
    return some (SMT.Term.symbApp "and" conds)

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
    -- Extensionality compares only valid inputs: Nat functions need not agree
    -- on negative values in the surrounding SMT Int sort.
    let pointwise := (smt| (= $appA $appB))
    let pointwise ←
      match ← binderGuard (binders.map (·.1)) shape.args with
      | none => pure pointwise
      | some g => pure (smt| (=> $g $pointwise))
    let premise := SMT.Term.forallE binders pointwise
    let aRef := SMT.Term.const a
    let bRef := SMT.Term.const b
    let premise ←
      match ← binderGuard #[a, b] #[ty, ty] with
      | none => pure premise
      | some valid => pure (smt| (and $valid $premise))
    TranslateM.emitCommand (.assert
      (.forallE #[(a, sort), (b, sort)]
        (smt| (=> $premise (= $aRef $bRef)))))

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
    let key := closureKey lam
    -- Captured SMT-bound variables, in a deterministic order.
    let st ← get
    let captures := (collectFVars lam).filter fun fid =>
      st.boundVars.contains fid || st.funVars.contains fid
    let replayHead ← mkLambdaFVars (captures.map mkFVar) lam
    if let some existing ← TranslateM.structuralSymbol? key then
      TranslateM.recordSymbolExpr existing replayHead
      let capArgs ← captures.mapM fun fid => emitTerm (.fvar fid)
      return if capArgs.isEmpty then .const existing
             else .app (.symb existing) capArgs
    let cloName ← TranslateM.symbolForStructural key "clo"
    TranslateM.recordSymbolExpr cloName replayHead
    let capSorts ← captures.mapM fun fid => do emitSort (← fid.getType)
    let (arrowSort, _) ← declareArrowSort lamTy
    TranslateM.emitCommand (.declFun cloName capSorts arrowSort)
    markFunDeclared cloName
    -- Quantify captures as well as lambda parameters in the defining equation.
    let mut binders : Array (String × SSort) := #[]
    let mut capRefs : Array SMT.Term := #[]
    for fid in captures do
      let nm := (st.boundVars.get? fid).getD ((st.funVars.get? fid).getD "c")
      let fty ← fid.getType
      binders := binders.push (nm, ← emitSort fty)
      capRefs := capRefs.push (.const nm)
    let cloApp := if capRefs.isEmpty then SMT.Term.const cloName
                  else SMT.Term.app (.symb cloName) capRefs
    let (paramBinders, bodyTerm) ← emitLambdaBody lam shape
    let lhs := SMT.Term.app (.symb appName)
      (#[cloApp] ++ paramBinders.map (fun (n, _) => SMT.Term.const n))
    let axiomBody := (smt| (= $lhs $bodyTerm))
    -- The defining equation holds at well-formed arguments and captures only; the body is
    -- a Lean term and has no meaning at a value outside the encoded type's image.
    let captureTys ← captures.mapM fun fid => fid.getType
    let axiomBody ←
      match ← binderGuard ((binders ++ paramBinders).map (·.1)) (captureTys ++ shape.args) with
      | none => pure axiomBody
      | some g => pure (smt| (=> $g $axiomBody))
    let allBinders := binders ++ paramBinders
    TranslateM.emitCommand (.assert
      (if allBinders.isEmpty then axiomBody else .forallE allBinders axiomBody))
    -- A closure at valid captures is an actual Lean function. Do not assert this
    -- for padding captures, which need not correspond to any Lean environment.
    if let some valid ← wfCondition lamTy cloApp then
      let valid ←
        match ← binderGuard (binders.map (·.1)) captureTys with
        | none => pure valid
        | some guard => pure (smt| (=> $guard $valid))
      TranslateM.emitCommand (.assert
        (if binders.isEmpty then valid else .forallE binders valid))
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
          -- Defunctionalized parameters use app; native parameters apply directly
          -- without allocating an unused Fn sort.
          if (← whnf ty).isArrow && (← TranslateM.getConfig).hoMode != .native then
            let (_, appSym) ← declareArrowSort ty
            bind (TranslateM.withFunVar x.fvarId! appSym (go (i + 1) e (acc.push x)))
          else if (← whnf ty).isArrow then
            bind (TranslateM.withFunVar x.fvarId! nm (go (i + 1) e (acc.push x)))
          else
            bind (go (i + 1) e (acc.push x))
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

  /-- Allocate an opaque carrier, without asserting that its values represent Lean
  inhabitants. Callers must either prove nonemptiness or exclude padding values
  with a guard (the finite `Array Empty` representation uses only its sentinel). -/
  partial def declareOpaqueCarrier (e : Expr) : TranslateM SSort := do
    let e ← instantiateMVars e
    checkSortClosed e
    let key : StructuralKey := { tag := "opaque-sort", typeExprs := #[e] }
    let hint := match e with | .const n _ => nameHint n | _ => "s"
    let name ← TranslateM.symbolForStructural key hint
    -- Retain the Lean type so Alethe replay can decode binders over this sort.
    TranslateM.recordSymbolExpr name e
    if !(← declaredSort name) then
      TranslateM.emitCommand (.declSort name 0)
      markSortDeclared name
    return .app (.symb name) #[]

  /-- Every actual Lean value is valid. Replay can therefore decode a validity
  predicate as `True` over the source type, even when that type is empty. -/
  partial def recordValidityPredicate (name : String) (ty : Expr) : TranslateM Unit := do
    let head ← withLocalDeclD `value ty fun value =>
      mkLambdaFVars #[value] (mkConst ``True)
    TranslateM.recordSymbolExpr name head

  /-- Pad a possibly empty carrier and restrict its Lean image with a predicate.
  Only actual terms are constrained to satisfy it; the SMT sort itself remains
  nonempty even when the predicate has no satisfying values. -/
  partial def declareUninterpretedSort (e : Expr) : TranslateM SSort := do
    let sort ← declareOpaqueCarrier e
    unless ← knownNonemptyCarrier e do
      let .app (.symb name) _ := sort | return sort
      let wf ← reserveWfSymbol name
      unless ← declaredFun wf do
        markFunDeclared wf
        if ← isEmptyType e then
          let x ← TranslateM.freshSymbol "empty"
          TranslateM.emitCommand (.defFun false wf #[(x, sort)]
            (.app (.symb "Bool") #[]) (smt| false))
        else
          TranslateM.emitCommand (.declFun wf #[sort] (.app (.symb "Bool") #[]))
        recordValidityPredicate wf e
    return sort

  /-- Whether sort translation actually selected Crush's finite representation
  for this Lean Array type. A user sort handler may replace it, in which case
  built-in operations and well-formedness predicates must both defer. -/
  partial def finiteArraySortSelected (arrayTy elem : Expr) : TranslateM Bool := do
    let actual ← emitSort arrayTy
    let key : StructuralKey := {
      tag := "finite-array", name := ``Array, typeExprs := #[elem]
    }
    let some sortName ← TranslateM.structuralSymbol? key | return false
    return actual == SSort.app (.symb sortName) #[]

  /-- Declare the finite representation of `Array elem`.

  Every well-formed value has a nonnegative length, well-formed elements at
  in-bounds indices, and one canonical sentinel at every out-of-bounds index.
  Canonicalizing the total-array tail is required for sound equality and
  congruence: without it, two SMT values could represent the same Lean array but
  remain distinguishable by equality or an uninterpreted function. -/
  partial def declareFiniteArray (elem : Expr) : TranslateM FiniteArrayEncoding := do
    let elem ← instantiateMVars elem
    checkSortClosed elem
    let key : StructuralKey := {
      tag := "finite-array", name := ``Array, typeExprs := #[elem]
    }
    if let some sortName ← TranslateM.structuralSymbol? key then
      let some sentinel ← TranslateM.structuralSymbol? (finiteArraySentinelKey elem)
        | throwError "internal error: finite Array sort `{sortName}` has no sentinel"
      return ← finiteArrayEncodingNames sortName sentinel
    let sortName ← TranslateM.symbolForStructural key "Array"
    let sentinel ←
      TranslateM.symbolForStructural (finiteArraySentinelKey elem) s!"{sortName}_outside"
    let enc ← finiteArrayEncodingNames sortName sentinel
    markSortDeclared sortName
    let elemSort ← emitSort elem
    let intSort := SSort.app (.symb "Int") #[]
    let dataSort := SSort.app (.symb "Array") #[intSort, elemSort]
    TranslateM.emitCommand (.declDatatypes #[(sortName, 0, {
      ctors := #[{
        name := enc.ctor
        selDecls := #[(enc.lenSel, intSort), (enc.dataSel, dataSort)]
      }]
    })])
    if !(← declaredFun sentinel) then
      markFunDeclared sentinel
      TranslateM.emitCommand (.declFun sentinel #[] elemSort)
    if ← declDatatypeWF sortName then
      let xName ← TranslateM.freshSymbol "a"
      let iName ← TranslateM.freshSymbol "i"
      let sort := SSort.app (.symb sortName) #[]
      let x := SMT.Term.const xName
      let i := SMT.Term.const iName
      let len := SMT.Term.app (.symb enc.lenSel) #[x]
      let data := SMT.Term.app (.symb enc.dataSel) #[x]
      let value := (smt| (select $data $i))
      let inside := (smt| (and (>= $i 0) (< $i $len)))
      let outsideCanonical := (smt| (= $value $(SMT.Term.const enc.sentinel)))
      let pointwise ←
        if ← isEmptyType elem then
          pure outsideCanonical
        else
          match ← wfCondition elem value with
          | none => pure (smt| (or $inside $outsideCanonical))
          | some elemWF =>
            pure (smt| (and (=> $inside $elemWF)
                            (=> (not $inside) $outsideCanonical)))
      let lengthWF :=
        if ← isEmptyType elem then (smt| (= $len 0)) else (smt| (>= $len 0))
      let body := (smt| (and $lengthWF
        $(SMT.Term.forallE #[(iName, intSort)] pointwise)))
      let wf ← reserveWfSymbol sortName
      TranslateM.emitCommand (.defFun false wf #[(xName, sort)]
        (.app (.symb "Bool") #[]) body)
    return enc

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
  partial def declareDatatype (n : Name) (typeArgs : Array Expr := #[])
      (sourceType? : Option Expr := none) :
      TranslateM String := do
    let typeArgs ← typeArgs.mapM instantiateMVars
    typeArgs.forM checkSortClosed
    -- Type instantiations must distinguish sorts, constructors, and selectors.
    let key : StructuralKey := { tag := "datatype", name := n, typeExprs := typeArgs }
    if let some name ← TranslateM.structuralSymbol? key then
      return name
    -- Emit the complete Lean mutual block together: selectors and validity
    -- predicates can reference sibling sorts. Shared type parameters key each member.
    let iv ← getConstInfoInduct n
    -- Reserve sibling sorts before visiting fields so recursion reuses their names.
    let mut memberSorts : Array (Name × String) := #[]
    for m in iv.all do
      let memberKey : StructuralKey := {
        tag := "datatype", name := m, typeExprs := typeArgs
      }
      let mSort ← TranslateM.symbolForStructural memberKey (nameHint m)
      -- Record concrete universe levels before recursive field-sort emission can
      -- encounter the declaration's uninstantiated universe parameters.
      if let some sourceType := sourceType? then
        let .const _ levels := sourceType.getAppFn
          | throwError "crush: internal — expected a datatype application"
        TranslateM.recordSymbolExpr mSort (mkAppN (mkConst m levels) typeArgs)
      markSortDeclared mSort
      memberSorts := memberSorts.push (m, mSort)
    let mut dtInfos : Array (String × Nat × DatatypeDecl) := #[]
    let mut memberWF : Array (String × Array (String × Array (String × Expr))) := #[]
    for (m, mSort) in memberSorts do
      let miv ← getConstInfoInduct m
      let mut ctorDecls : Array CtorDecl := #[]
      -- Field descriptors for the wf axiom: per ctor, the selectors needing a guard.
      let mut wfParts : Array (String × Array (String × Expr)) := #[]
      for ctorName in miv.ctors do
        let ctorSym ← reserveCtorSymbol mSort ctorName
        let ctorInfo ← getConstInfoCtor ctorName
        -- Specialize fields at the datatype parameters before translating their sorts.
        let ctorTy ← instantiateForall ctorInfo.type typeArgs
        let (selDecls, guards) ← forallTelescopeReducing ctorTy fun args _ => do
          let mut sels : Array (String × SSort) := #[]
          let mut gs : Array (String × Expr) := #[]
          for i in [0:args.size] do
            let fieldTy ← inferType args[i]!
            let s ← emitSort fieldTy
            let selName ← reserveSelSymbol mSort ctorName i
            sels := sels.push (selName, s)
            if (← needsWFGuard fieldTy) then
              gs := gs.push (selName, fieldTy)
          return (sels, gs)
        ctorDecls := ctorDecls.push { name := ctorSym, selDecls }
        wfParts := wfParts.push (ctorSym, guards)
      dtInfos := dtInfos.push (mSort, 0, { ctors := ctorDecls })
      memberWF := memberWF.push (mSort, wfParts)
    TranslateM.emitCommand (.declDatatypes dtInfos)
    -- Reserve predicates before defining the mutual block with define-funs-rec.
    -- Quantified recursive equations can make even unrelated ground queries unknown.
    let mut needDef : Array (String × Array (String × Array (String × Expr))) := #[]
    for (mSort, wfParts) in memberWF do
      if ← declDatatypeWF mSort then
        needDef := needDef.push (mSort, wfParts)
    let mut wfDefs : Array FunDef := #[]
    for (mSort, wfParts) in needDef do
      wfDefs := wfDefs.push (← datatypeWFDef mSort wfParts)
    unless wfDefs.isEmpty do
      TranslateM.emitCommand (.defFunsRec wfDefs)
    let some (_, nSort) := memberSorts.find? (·.1 == n)
      | throwError "crush: internal — `{n}` missing from its own mutual block"
    return nSort

  /-- Whether values of `ty` occupy a *proper subset* of their SMT sort, so a
  quantifier over them needs a guard. True for `Nat` (encoded as `Int`) and for any
  datatype that transitively contains such a field.

  `visiting` holds the instantiated types already on the stack. Re-entering the
  same recursive type contributes nothing new. Distinct applications of the same
  constructor must still be traversed: `Int × (Nat × Nat)` needs the guards of its
  inner product even though the outer product has already been visited. -/
  partial def needsWFGuard (ty : Expr) (visiting : Std.HashSet Expr := {}) :
      TranslateM Bool := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then return true
    if let some elem ← finiteArrayElem? ty then
      return ← finiteArraySortSelected ty elem
    if let some shape ← arrowShape? ty then
      if (← TranslateM.getConfig).hoMode == .native then
        if ← shape.args.anyM (needsWFGuard · visiting) then return true
      else if ← knownNonemptyDefunctionalizedArrow ty shape then
        return false
      return ← needsWFGuard shape.res visiting
    let some (n, typeArgs) ← supportedDatatypeType? ty | do
      discard <| emitSort ty
      let key : StructuralKey := { tag := "opaque-sort", typeExprs := #[ty] }
      if (← TranslateM.structuralSymbol? key).isSome then
        return !(← knownNonemptyCarrier ty)
      return false
    if visiting.contains ty then return false
    let visiting := visiting.insert ty
    -- Inspect instantiated fields so Option Nat receives guards while Option Int does not.
    let iv ← getConstInfoInduct n
    iv.ctors.anyM fun ctorName => do
      let ci ← getConstInfoCtor ctorName
      let ctorTy ← instantiateForall ci.type typeArgs
      forallTelescopeReducing ctorTy fun args _ =>
        args.anyM fun a => do
          needsWFGuard (← inferType a) visiting

  /-- Reserve `wf_T` (returns whether it was newly reserved, i.e. still needs its
  definition). The `wf` predicate carves the Lean type's image out of its freely-generated
  SMT sort; its definition (`datatypeWFDef`) is stated in *selector* form,

  ```
  (define-fun-rec wf_T ((x T)) Bool
    (and (=> ((_ is C₁) x) ⟨guards on C₁'s fields of x⟩) …))
  ```

  which z3 handles far better than the constructor-applied form. When no field needs a
  guard the predicate is constantly `true`, so the quantifier guard costs nothing.

  Reservation and body construction are split so a mutual block can place all members in
  one `define-funs-rec` command — a member's body may reference a sibling's `wf`.
  `declareDatatype` drives the two in that order across the whole block. -/
  partial def declDatatypeWF (sortName : String) : TranslateM Bool := do
    let wf ← reserveWfSymbol sortName
    if let some sourceType := (← get).nameToExpr[sortName]? then
      recordValidityPredicate wf sourceType
    if ← declaredFun wf then return false
    markFunDeclared wf
    return true

  /-- Build one member of a mutually recursive well-formedness definition. -/
  partial def datatypeWFDef (sortName : String)
      (parts : Array (String × Array (String × Expr))) : TranslateM FunDef := do
    let wf ← reserveWfSymbol sortName
    let sort := SSort.app (.symb sortName) #[]
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
                  else SMT.Term.symbApp "and" fieldConds
      let tester := testerApp ctorSym x
      conjuncts := conjuncts.push (smt| (=> $tester $body))
    let rhs :=
      if conjuncts.isEmpty then (smt| true)
      else if conjuncts.size == 1 then conjuncts[0]!
      else SMT.Term.symbApp "and" conjuncts
    return {
      name := wf
      args := #[(v, sort)]
      resSort := .app (.symb "Bool") #[]
      body := rhs
    }

  /-- The well-formedness condition on an SMT term of Lean type `ty`: `≥ 0` for
  `Nat`, `wf_T` for a guarded datatype, `none` when nothing is needed. -/
  partial def wfCondition (ty : Expr) (t : SMT.Term) : TranslateM (Option SMT.Term) := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then
      return some (smt| (>= $t 0))
    if let some elem ← finiteArrayElem? ty then
      unless ← finiteArraySortSelected ty elem do return none
      let enc ← declareFiniteArray elem
      let wf ← reserveWfSymbol enc.sortName
      return some (.app (.symb wf) #[t])
    if let some shape ← arrowShape? ty then
      if (← TranslateM.getConfig).hoMode == .native then
        return ← nativeFunctionWF shape t
      if !(← needsWFGuard shape.res) then return none
      let (sort, _) ← declareArrowSort ty
      if ← knownNonemptyDefunctionalizedArrow ty shape then return none
      let .app (.symb sortName) _ := sort | return none
      let wf ← reserveWfSymbol sortName
      return some (.app (.symb wf) #[t])
    let some (n, typeArgs) ← supportedDatatypeType? ty | do
      discard <| emitSort ty
      let key : StructuralKey := { tag := "opaque-sort", typeExprs := #[ty] }
      let some sortName ← TranslateM.structuralSymbol? key | return none
      if ← knownNonemptyCarrier ty then return none
      let wf ← reserveWfSymbol sortName
      return some (.app (.symb wf) #[t])
    if !(← needsWFGuard ty) then return none
    let sortName ← declareDatatype n typeArgs (some ty)
    let wf ← reserveWfSymbol sortName
    return some (.app (.symb wf) #[t])

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
    let e := (← instantiateMVars e).consumeMData
    -- Proofs are erased, never inhabitants of an SMT carrier. In particular a
    -- hypothetical proof of False must not generate an unconditional witness.
    if ← isProof e then
      throwError "crush: cannot translate a proof-valued term as an SMT value"
    -- Zeta-reduce a let (including one in application-head position) before it
    -- can become an opaque symbol and lose dependencies on enclosing binders.
    if let .letE _ _ value body _ := e.getAppFn.consumeMData then
      return ← emitTerm (mkAppN (body.instantiate1 value) e.getAppArgs)
    -- A quantifier-bound variable renders as its SMT name, never a declaration.
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- General handlers retain first refusal over all built-in mappings.
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
    -- Dispatch targeted lowerings after general overrides.
    let (fn, args) := getAppFnArgs' e
    if let .const head _ := fn then
      if ← hasLoweringsFor head then
        let ctx : TranslationCtx := {
          fn, args
          emitTerm := emitTerm
          emitSort := emitSort
          declare  := declareViaThunk }
        for lowering in (← getLoweringsFor head) do
          if let some t ← lowering ctx then
            return t
    -- Use immediate result heads or syntactic dependent codomains; aliases remain distinct.
    if ← hasResultLowerings then
      let ty ← inferType e
      if let some resultHead ← resultHead? ty then
        if ← hasResultLoweringsFor resultHead then
          let ctx : TranslationCtx := {
            fn, args
            emitTerm := emitTerm
            emitSort := emitSort
            declare  := declareViaThunk }
          for lowering in (← getResultLoweringsFor resultHead) do
            if let some t ← lowering ctx then
              return t
    let logicalClassProjection ← isLogicalClassProjection fn
    -- Expose the selected instance for partial logical projections before HO
    -- encoding turns the remaining predicate into a function value.
    if logicalClassProjection && (← whnf (← inferType e)).isArrow then
      let reduced ← withTransparency .instances <| whnf e
      if reduced != e then
        return ← emitTerm reduced
    -- Proof irrelevance also covers proofs of function-shaped propositions.
    -- Handle their equality before the higher-order function encoder sees it.
    match_expr e with
    | Eq ty _ _ => if ← isProp ty then return (smt| true)
    | _ => pure ()
    if let some t ← hoTerm? e then
      return t
    match ← structural? e with
    | some t => return t
    | none =>
      if let some t ← ctorApp? fn args then
        return t
      if let some t ← projApp? fn args then
        return t
      -- Only intrinsically logical fields expose instance semantics; data
      -- projections merely instantiated at Bool do not qualify.
      if logicalClassProjection then
        let reduced ← withTransparency .instances <| whnf e
        if reduced != e then
          return ← emitTerm reduced
      if let .const head _ := fn then
        -- Unfold nullary value aliases only; definitions with arguments may be
        -- recursive or have dedicated lowerings.
        if args.isEmpty then
          if ← Lean.isReducible head then
            let reduced ← withReducible <| whnf e
            if reduced != e then
              return ← emitTerm reduced
          else if ← Lean.isImplicitReducible head then
            let reduced ← withTransparency .instances <| whnf e
            if reduced != e then
              return ← emitTerm reduced
      defaultApp fn args

  /-- Higher-order forms: λ-abstractions, partial applications, applications whose
  head is a function *value*, and equations between function-typed terms. Returns
  `none` for fully-applied first-order constants and free function symbols, which
  the ordinary declaration path handles directly.

  This is the entry point for the encoding described in `HOEncoding.lean`, and the
  fix for the false-`unsat` that arose when a function-typed bound variable was
  declared as an unrelated `declare-fun`. -/
  partial def hoTerm? (e : Expr) : TranslateM (Option SMT.Term) := do
    let mode := (← TranslateM.getConfig).hoMode
    if e.isLambda then
      -- Dependent function values lack a fixed ArrowShape. Defer them instead
      -- of allocating a nondependent function sort.
      if (← arrowShape? (← inferType e)).isSome then
        if mode == .native then
          return some (← emitNativeLambda e)
        return some (← emitClosure e)
      return none
    -- Materialize residual function values before later applications can
    -- become unrelated first-order symbols.
    if (← whnf (← inferType e)).isArrow then
      return some (← emitFunValue e)
    -- Apply quantified function values through their recorded app symbol,
    -- never through a fresh declaration detached from the binder.
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .fvar fid := fn then
      if let some appSym ← TranslateM.funVar? fid then
        if args.isEmpty then
          if let some vname ← TranslateM.boundVar? fid then
            return some (.const vname)
          return none
        let some vname ← TranslateM.boundVar? fid | return none
        -- Defunctionalized app consumes the full flattened telescope. Represent
        -- partial applications as closures of the residual arrow type; native
        -- application can remain partial.
        if mode != .native then
          if let some shape ← arrowShape? (← whnf (← fid.getType)) then
            if args.size < shape.args.size then
              return some (← emitFunValue e)
        let sargs ← args.mapM emitTerm
        if mode == .native then
          return some (.app (.symb vname) sargs)
        return some (.app (.symb appSym) (#[.const vname] ++ sargs))
    -- Apply computed function heads as values, preserving their identity
    -- instead of declaring a first-order symbol for the head syntax.
    unless args.isEmpty do
      unless fn.isConst || fn.isFVar do
        if let some shape ← arrowShape? (← inferType fn) then
          if args.size == shape.args.size then
            let sfn ← emitFunValue fn
            let sargs ← args.mapM emitTerm
            if mode == .native then
              -- SMT-LIB application syntax requires an identifier in head position.
              -- A local `let` gives an arbitrary function value such a name.
              let name ← TranslateM.freshSymbol "hof"
              return some (.letE #[(name, sfn)] (.app (.symb name) sargs))
            let (_, appSym) ← declareArrowSort (← inferType fn)
            return some (.app (.symb appSym) (#[sfn] ++ sargs))
    -- Function equality compares encoded values and requires extensionality.
    match_expr e with
    | Eq ty a b =>
      if (← whnf ty).isArrow then
        -- Native equality supplies extensionality; defunctionalization must assert it.
        if mode != .native then
          emitExtensionality ty
        return some (smt| (= $(← emitFunValue a) $(← emitFunValue b)))
      return none
    | _ => return none

  /-- One shared padding value per native codomain, used only outside the
  corresponding Lean argument domain. It need not be a Lean inhabitant. -/
  partial def nativeOutsideValue (ty : Expr) : TranslateM SMT.Term := do
    let key : StructuralKey := { tag := "native-outside", typeExprs := #[ty] }
    let name ← TranslateM.symbolForStructural key "outside"
    unless ← declaredFun name do
      let sort ← emitSort ty
      markFunDeclared name
      TranslateM.emitCommand (.declFun name #[] sort)
    return .const name

  /-- A native function must produce valid results at valid arguments and agree
  with the canonical extension outside its Lean domain. This predicate restricts
  quantified functions as well as function-valued results and datatype fields. -/
  partial def nativeFunctionWF (shape : ArrowShape) (t : SMT.Term) :
      TranslateM (Option SMT.Term) := do
    let f ← TranslateM.freshSymbol "wf_fn"
    let mut binders : Array (String × SSort) := #[]
    for ty in shape.args do
      binders := binders.push (← TranslateM.freshSymbol "wf_arg", ← emitSort ty)
    let value := SMT.Term.app (.symb f) (binders.map fun b => SMT.Term.const b.1)
    let result ← wfCondition shape.res value
    let domain ← binderGuard (binders.map (·.1)) shape.args
    let condition ← match domain, result with
      | none, none => return none
      | none, some valid => pure valid
      | some domain, result =>
        let outside ← nativeOutsideValue shape.res
        let canonical := (smt| (=> (not $domain) (= $value $outside)))
        match result with
        | none => pure canonical
        | some valid => pure (smt| (and (=> $domain $valid) $canonical))
    return some (.letE #[(f, t)] (.forallE binders condition))

  /-- A native higher-order `lambda` term, for HO-capable backends. -/
  partial def emitNativeLambda (lam : Expr) : TranslateM SMT.Term := do
    let lamTy ← whnf (← inferType lam)
    let some shape ← arrowShape? lamTy
      | throwError "crush: internal — native lambda of non-arrow type {lamTy}"
    let (binders, body) ← emitLambdaBody lam shape
    -- Native equality compares the entire SMT domain. Equal Lean functions
    -- therefore need the same extension at negative Nats and other padding.
    let body ← match ← binderGuard (binders.map (·.1)) shape.args with
      | none => pure body
      | some valid =>
        let outside ← nativeOutsideValue shape.res
        pure (smt| (ite $valid $body $outside))
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
    -- Translate function-valued conditionals directly to avoid repeatedly
    -- eta-expanding the same head while constructing its closure equation.
    match_expr e with
    | ite _ c _ a b =>
      return (smt| (ite $(← emitTerm c) $(← emitFunValue a) $(← emitFunValue b)))
    | cond _ c a b =>
      return (smt| (ite $(← emitTerm c) $(← emitFunValue a) $(← emitFunValue b)))
    | _ => pure ()
    -- Reduce syntactic lets without unfolding arbitrary function definitions.
    if e.isLet then
      let reduced ← whnf e
      if reduced != e then return ← emitFunValue reduced
    -- Keep projections as arrow-sort values so later app calls preserve their identity.
    if e.isProj then
      return ← defaultApp e #[]
    -- Eta-expand named functions into closures or native lambdas.
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
    let some structArg := args[info.numParams]? | return none
    let structTy ← whnf (← inferType structArg)
    if (← finiteArrayElem? structTy).isSome then return none
    let some (_, typeArgs) ← supportedDatatypeType? structTy | return none
    let sortName ← declareDatatype info.ctorName.getPrefix typeArgs (some structTy)
    let sel ← reserveSelSymbol sortName info.ctorName info.i
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
    let resTy ← whnf (← inferType (mkAppN fn args))
    if (← finiteArrayElem? resTy).isSome then return none
    let some (_, typeArgs) ← supportedDatatypeType? resTy | return none
    let sortName ← declareDatatype ci.induct typeArgs (some resTy)
    let valueArgs := args.extract ci.numParams args.size
    let sargs ← valueArgs.mapM emitTerm
    let ctor ← reserveCtorSymbol sortName cn
    return some (.app (.symb ctor) sargs)

  /-- Recognize the built-in logical/arithmetic structure. Returns `none` to let
  handlers / the default path take over. -/
  partial def structural? (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .const ``True _  => return some (smt| true)
    | .const ``False _ => return some (smt| false)
    | .const ``Bool.true _  => return some (smt| true)
    | .const ``Bool.false _ => return some (smt| false)
    | .lit (.strVal s) => return some (.lit (.str s))
    | _ =>
    -- Built-in operator semantics require the fixed canonical dictionary.
    -- Custom instances fall through to uninterpreted translation.
    if ← isNonCanonicalOverload e then return none
    match e with
    | _ =>
    -- Bit-vectors dispatch by type; String operations use DefaultLowerings.
    match ← bitvecTerm? e with
    | some t => return some t
    | none =>
    -- Only Nat and Int use SMT integer operators. Other carriers must remain
    -- uninterpreted even when their overloaded dictionaries are canonical.
    if let some carriers := integerOverloadCarriers? e then
      unless ← isHomogeneousIntegerCarrier carriers do return none
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      -- Only Nat and Int use integer literals. Other OfNat values may reduce
      -- to datatype constructors; reduce those without unfolding theory numerals.
      let ty ← whnf (← inferType e)
      if ty.isConstOf ``Nat || ty.isConstOf ``Int then
        return (← getNatLit? e).map (.lit <| .num ·)
      else
        let e' ← whnf e
        if e' == e then return none else return some (← emitTerm e')
    | Neg.neg _ _ a =>
      return some (smt| (- $(← emitTerm a)))
    | HDiv.hDiv _ _ _ _ a b =>
      -- Match Lean's zero-divisor value rather than leaving SMT division underspecified.
      return some (intDivGuard "div" (← emitTerm a) (← emitTerm b))
    | HMod.hMod _ _ _ _ a b =>
      return some (intDivGuard "mod" (← emitTerm a) (← emitTerm b))
    | _ =>
    match_expr e with
    | And a b => return some (smt| (and $(← emitTerm a) $(← emitTerm b)))
    | Or a b  => return some (smt| (or $(← emitTerm a) $(← emitTerm b)))
    | Not a   => return some (smt| (not $(← emitTerm a)))
    -- Bool functions share SMT operators with Prop connectives but have distinct Lean heads.
    | not a   => return some (smt| (not $(← emitTerm a)))
    | and a b => return some (smt| (and $(← emitTerm a) $(← emitTerm b)))
    | or a b  => return some (smt| (or $(← emitTerm a) $(← emitTerm b)))
    | xor a b => return some (smt| (xor $(← emitTerm a) $(← emitTerm b)))
    | bne carrier inst a b =>
      unless ← hasLawfulBEq carrier inst do return none
      return some (smt| (not (= $(← emitTerm a) $(← emitTerm b))))
    | BEq.beq carrier inst a b =>
      unless ← hasLawfulBEq carrier inst do return none
      return some (smt| (= $(← emitTerm a) $(← emitTerm b)))
    | Iff a b => return some (smt| (= $(← emitTerm a) $(← emitTerm b)))
    | Eq _ a b => return some (smt| (= $(← emitTerm a) $(← emitTerm b)))
    | Ne _ a b => return some (smt| (not (= $(← emitTerm a) $(← emitTerm b))))
    | HAdd.hAdd _ _ _ _ a b => return some (smt| (+ $(← emitTerm a) $(← emitTerm b)))
    | HMul.hMul _ _ _ _ a b => return some (smt| (* $(← emitTerm a) $(← emitTerm b)))
    | HSub.hSub _ _ _ _ a b =>
      -- Nat subtraction truncates at zero; plain SMT subtraction would admit negatives.
      let sa ← emitTerm a
      let sb ← emitTerm b
      if (← isNatTyped e) then
        return some (smt| (ite (>= $sa $sb) (- $sa $sb) 0))
      else
        return some (smt| (- $sa $sb))
    -- Expand min/max after validating the carrier and overloaded dictionary.
    | max _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (smt| (ite (>= $sa $sb) $sa $sb))
    | min _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (smt| (ite (<= $sa $sb) $sa $sb))
    | Nat.succ a => return some (smt| (+ $(← emitTerm a) 1))
    -- Only canonical casts into Nat or Int are identities in this encoding.
    -- Other dictionaries remain uninterpreted, without any injectivity assumption.
    | Nat.cast target inst a =>
      let target ← whnf target
      let expected ←
        if target.isConstOf ``Int then pure (mkConst ``instNatCastInt)
        else if target.isConstOf ``Nat then pure (mkConst ``instNatCastNat)
        else return none
      unless ← isDefEqRigid inst expected do return none
      return some (← emitTerm a)
    | LE.le _ _ a b => return some (smt| (<= $(← emitTerm a) $(← emitTerm b)))
    | LT.lt _ _ a b => return some (smt| (< $(← emitTerm a) $(← emitTerm b)))
    | GE.ge _ _ a b => return some (smt| (>= $(← emitTerm a) $(← emitTerm b)))
    | GT.gt _ _ a b => return some (smt| (> $(← emitTerm a) $(← emitTerm b)))
    | ite _ c _ a b =>
      return some (smt| (ite $(← emitTerm c) $(← emitTerm a) $(← emitTerm b)))
    | dite _ c _ a b =>
      -- Proof binders are not runtime inputs. Translate each branch under its
      -- hypothesis and use the actual proposition to select the branch.
      let yes ← withLocalDeclD `hp c fun hp => emitTerm ((mkApp a hp).headBeta)
      let no ← withLocalDeclD `hnp (mkNot c) fun hnp => emitTerm ((mkApp b hnp).headBeta)
      return some (smt| (ite $(← emitTerm c) $yes $no))
    | cond _ b t e =>
      return some (smt| (ite $(← emitTerm b) $(← emitTerm t) $(← emitTerm e)))
    | _ =>
      if e.isArrow then
        let some t ← tryImplication e | return none
        return some t
      match e with
      | .forallE _ ty body _ =>
        if (← isProp ty) then
          -- A proof binder denotes implication. Open it with a real local so dependent
          -- uses remain closed; defaultApp erases proof arguments with its result guard.
          let a ← emitTerm ty
          if body.hasLooseBVar 0 then
            let b ← withLocalDeclD `hp ty fun hp => emitTerm (body.instantiate1 hp)
            return some (smt| (=> $a $b))
          let b ← emitTerm body
          return some (smt| (=> $a $b))
        else
          quantifier true ty body
      | .app (.app (.const ``Exists _) _) (.lam _ ty body _) =>
        if ← isProp ty then
          -- A proof exists exactly when its proposition holds. Proof irrelevance
          -- permits a fresh proof local when the predicate mentions its witness.
          let a ← emitTerm ty
          let b ← withLocalDeclD `hp ty fun hp => emitTerm (body.instantiate1 hp)
          return some (smt| (and $a $b))
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
    -- Conversions and numerals carry their own width; other operators use operand types.
    match_expr e with
    | BitVec.ofNat w n =>
      let some wv ← natValue? w | return none
      match ← natValue? n with
      | some nv => return some (bvLit wv nv)
      | none =>
        -- int2bv preserves symbolic dependence and wraps modulo 2^w like BitVec.ofNat.
        return some (.app (.indexed "int2bv" #[.inr wv]) #[← emitTerm n])
    | OfNat.ofNat ty n _ =>
      unless ← hasExpectedOfNatInstance e do return none
      -- OfNat is shared with integer types, so inspect its carrier before emitting a literal.
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
    | Complement.complement _ _ a => return some (smt| (bvnot $(← emitTerm a)))
    | Neg.neg _ _ a => return some (smt| (bvneg $(← emitTerm a)))
    -- Unsigned division needs a zero-divisor guard: Lean returns zero while
    -- bvudiv returns all ones. Unsigned remainder already agrees at zero.
    | HDiv.hDiv _ _ _ _ a b => return some (bvDivGuard "bvudiv" w (← emitTerm a) (← emitTerm b))
    | HMod.hMod _ _ _ _ a b => bin "bvurem" a b
    -- Recognize named BitVec operations as well as their overloaded forms.
    | BitVec.add _ a b => bin "bvadd" a b
    | BitVec.sub _ a b => bin "bvsub" a b
    | BitVec.mul _ a b => bin "bvmul" a b
    | BitVec.neg _ a => return some (smt| (bvneg $(← emitTerm a)))
    | BitVec.not _ a => return some (smt| (bvnot $(← emitTerm a)))
    | BitVec.and _ a b => bin "bvand" a b
    | BitVec.or _ a b  => bin "bvor" a b
    | BitVec.xor _ a b => bin "bvxor" a b
    | BitVec.udiv _ a b => return some (bvDivGuard "bvudiv" w (← emitTerm a) (← emitTerm b))
    | BitVec.umod _ a b => bin "bvurem" a b
    | BitVec.sdiv _ a b => return some (bvDivGuard "bvsdiv" w (← emitTerm a) (← emitTerm b))
    | BitVec.srem _ a b => bin "bvsrem" a b
    | BitVec.smod _ a b => bin "bvsmod" a b
    -- BitVec order is unsigned, matching bvult and bvule.
    | LT.lt _ _ a b => bin "bvult" a b
    | LE.le _ _ a b => bin "bvule" a b
    | GT.gt _ _ a b => bin "bvugt" a b
    | GE.ge _ _ a b => bin "bvuge" a b
    | BitVec.ult _ a b => bin "bvult" a b
    | BitVec.ule _ a b => bin "bvule" a b
    | BitVec.slt _ a b => bin "bvslt" a b
    | BitVec.sle _ a b => bin "bvsle" a b
    -- SMT requires equal operand widths; shiftOp preserves and saturates the full amount.
    | HShiftLeft.hShiftLeft _ _ _ _ a b => shiftOp "bvshl" w a b
    | HShiftRight.hShiftRight _ _ _ _ a b => shiftOp "bvlshr" w a b
    | BitVec.sshiftRight _ a b => shiftOp "bvashr" w a b
    | BitVec.sshiftRight' _ _ a b => shiftOp "bvashr" w a b
    | BitVec.shiftLeft _ a b => shiftOp "bvshl" w a b
    | BitVec.ushiftRight _ a b => shiftOp "bvlshr" w a b
    -- SMT rotation amounts are literal indices; both semantics reduce them modulo width.
    | BitVec.rotateLeft _ a b => rotateOp "rotate_left" a b
    | BitVec.rotateRight _ a b => rotateOp "rotate_right" a b
    | BitVec.setWidth _ target x =>
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize false xw tv (← emitTerm x))
    | BitVec.zeroExtend _ target x =>
      -- zeroExtend is a distinct declaration with the same unsigned resize as setWidth.
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize false xw tv (← emitTerm x))
    | BitVec.signExtend _ target x =>
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize true xw tv (← emitTerm x))
    | BitVec.extractLsb _ hi lo x =>
      -- Convert inclusive bounds to a slice length. Empty slices have no SMT
      -- extract representation and remain uninterpreted.
      let some hv ← natValue? hi | return none
      let some lv ← natValue? lo | return none
      let some xw ← bvWidthOf? x | return none
      if hv < lv then return none
      let len := hv + 1 - lv
      let sx ← emitTerm x
      if lv ≥ xw then return some (bvLit len 0)
      let avail := xw - lv
      let sliced := bvExtract (min (lv + len) xw - 1) lv sx
      return some (if len ≤ avail then sliced else bvExtend false (len - avail) sliced)
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
      -- Both append and SMT concat put the first operand in the high bits.
      return some (smt| (concat $(← emitTerm a) $(← emitTerm b)))
    -- toNat is unsigned, toInt is signed two's-complement, and ofInt wraps.
    | BitVec.toNat _ a => return some (smt| (bv2nat $(← emitTerm a)))
    | BitVec.toInt _ a => return some (smt| (sbv_to_int $(← emitTerm a)))
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
      let sb ← emitTerm b
      let shifted := SMT.Term.symbApp op #[sa, bvResize false bw w sb]
      if bw > w then
        -- Truncating a wide amount would wrap, e.g. 256#16 to 0#8. Compare
        -- the full amount first; shifting by the width gives zero or sign-fill.
        let saturated := SMT.Term.symbApp op #[sa, bvLit w w]
        return some (smt| (ite (bvuge $sb $(bvLit bw w)) $saturated $shifted))
      return some shifted
    if (← whnf (← inferType b)).isConstOf ``Nat then
      let some bv ← natValue? b | return none
      -- Saturate at the width: both Lean and SMT yield 0 (or sign-fill) there, and
      -- the literal must fit in `w` bits to be representable.
      return some (.symbApp op #[sa, bvLit w (min bv w)])
    return none

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
      return some (smt| (=> $(← emitTerm ty) $(← emitTerm body)))
    | _ => return none

  /-- Translate `∀ (x : ty), body` / `∃ (x : ty), body` over a non-Prop sort.
  A fresh SMT-bound variable is introduced; a `Nat` domain gets a `≥ 0` guard.
  The SMT quantifier uses the *named* binder form (not de Bruijn), so we register
  the introduced fvar → name mapping and reference it directly. -/
  partial def quantifier (isForall : Bool) (ty body : Expr) : TranslateM (Option SMT.Term) := do
    let sort ← emitSort ty
    let vname ← TranslateM.freshSymbol "q"
    -- Open the binder with a real local tied to its SMT name. Function locals
    -- also need a funVar mapping so applications cannot detach from the quantifier.
    let inner ← withLocalDeclD (Name.mkSimple vname) ty fun x => do
      let k := emitTerm (body.instantiate1 x)
      if (← whnf ty).isArrow then
        -- Native function locals need no app symbol, but still need the funVar marker.
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
      if isForall then return (smt| (=> $cond $body))
      else return (smt| (and $cond $body))

  /-- Uninterpreted-function fallback: declare the head, translate the args.

  If the head's result type is `Nat`, we additionally emit its non-negativity
  well-formedness constraint (`emitNatWF`) so the `Int` encoding cannot assign it
  a negative value — closing the soundness hole for `Nat`-valued atoms/functions
  (a bare `n : Nat` free variable, `f : α → Nat`, etc.). -/
  partial def defaultApp (fn : Expr) (args : Array Expr) : TranslateM SMT.Term := do
    -- Partition signature parameters from SMT value arguments before declaring the symbol.
    let partition ← partitionDefaultAppArgs fn args
    -- Every SMT binder dependency must be an explicit argument of this symbol.
    -- A dependency hidden in the head or an erased type/instance would
    -- collapse distinct binder instantiations into a single SMT constant.
    let st ← get
    let checkClosed (term : Expr) : TranslateM Unit := do
      if (Lean.collectFVars {} term).fvarIds.any
          (fun id => st.boundVars.contains id || st.funVars.contains id) then
        throwError "crush: cannot erase a bound-variable dependency in an uninterpreted application:{indentExpr term}"
    checkClosed fn
    for i in [:args.size] do
      unless partition.valuePositions.contains i || (← isProof args[i]!) do
        checkClosed args[i]!
    let valueArgs := partition.values
    let appExpr := mkAppN fn args
    -- Preserve aliases for `emitSort`: a user sort handler may intentionally target a
    -- `def`-defined type. Structural keys normalize type components separately.
    let resTy ← instantiateMVars (← inferType appExpr)
    -- Key the full instantiated signature, including erased instances: polymorphic
    -- projections may otherwise reuse a declaration with incompatible function sorts.
    let instanceKeys ← partition.instances.mapM fun instanceArg => do
      let instanceArg ← instantiateMVars instanceArg
      Meta.withTransparency .instances <| Meta.reduceAll instanceArg
    let argTypes ← valueArgs.mapM fun a => do instantiateMVars (← inferType a)
    let key : StructuralKey := {
      tag := s!"function-signature:{partition.types.size}:{instanceKeys.size}:{argTypes.size}"
      exprs := #[fn] ++ instanceKeys
      typeExprs := partition.types ++ argTypes ++ #[resTy] }
    let hint ← headHint fn
    let name ← TranslateM.symbolForStructural key hint
    unless (← get).nameToExpr.contains name do
      TranslateM.recordSymbolExpr name
        (← defaultReplayHead fn args partition.valuePositions)
    if !(← declaredFun name) then
      let argSorts ← valueArgs.mapM (fun a => do emitSort (← inferType a))
      let resSort ← emitSort resTy
      TranslateM.emitCommand (.declFun name argSorts resSort)
      markFunDeclared name
      -- Erasing a proof argument can enlarge the domain of a partial Lean
      -- function. Extending it to a possibly empty result carrier is not sound.
      -- Until its preconditions are carried by the function signature, refuse
      -- this case instead of asserting an unconditional result inhabitant.
      if !(← knownNonemptyCarrier resTy) && (← args.anyM fun a => isProof a) then
        throwError "crush: cannot translate a possibly empty result type after erasing proof arguments: {resTy}"
      emitResultWF name argSorts argTypes resTy
    -- Function arguments must inhabit their arrow sort; eta-expand named functions
    -- instead of passing first-order symbols where function values are expected.
    let sargs ← valueArgs.mapM fun a => do
      if ← isFunctionType (← inferType a) then emitFunValue a else emitTerm a
    return .app (.symb name) sargs

  /-- Constrain an uninterpreted symbol's *result* to the well-formed subset of its
  sort — the `Nat`-valued case (`f : α → Nat` is never negative) generalized to any
  guarded type. Nullary symbols get a bare assertion; higher arity a quantified one
  over fresh variables. Emitted once, at declaration time. -/
  partial def emitResultWF (name : String) (argSorts : Array SSort)
      (argTypes : Array Expr) (resTy : Expr) :
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
      let c ←
        match ← binderGuard (binders.map (·.1)) argTypes with
        | none => pure c
        | some guard => pure (smt| (=> $guard $c))
      TranslateM.emitCommand (.assert (.forallE binders c))

  partial def headHint (fn : Expr) : TranslateM String := do
    match fn with
    | .const n _ => return nameHint n
    | .fvar fid => return nameHint (← fid.getUserName)
    | _ => return "f"
end

end Crush
