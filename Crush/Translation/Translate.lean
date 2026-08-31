import Lean
import Crush.SMT.Syntax
import Crush.SMT.Quote
import Crush.Translation.Monad
import Crush.Translation.Attr
import Crush.Translation.Theories
import Crush.Translation.HOEncoding
import Crush.Metatheory.Reification.Reify
import Crush.Metatheory.Reification.Datatype
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
open Metatheory.SMT.Datatype (wfDef)

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

/-- Whether the instance argument at position `i` of the application `e` is the
canonical global instance.

Recognizing `HAdd.hAdd _ _ _ inst a b` as SMT `+` assumes `inst` is the *standard*
instance. A user can supply another — `⟨fun _ _ => 99⟩` is a legal `HAdd Int Int Int`
— and then `1 + 2` is `99`, not `3`. Matching on the head alone therefore imports
arithmetic that does not hold, and lets the solver prove false goals.

Local instances are disabled while synthesizing the baseline. Otherwise a local
override is exactly what synthesis picks and would compare equal to itself. Returns
`false` when synthesis fails, so an exotic instance degrades to an uninterpreted
symbol rather than being silently mistranslated. -/
def hasCanonicalInstance (e : Expr) (i : Nat) : TranslateM Bool := do
  let args := e.getAppArgs
  let some inst := args[i]? | return false
  let instTy ← inferType inst
  try
    let lctx ← getLCtx
    let canon ← withLCtx lctx {} do synthInstance instTy
    isDefEqReadOnly inst canon
  catch _ =>
    -- Synthesis failed: we cannot confirm the instance is standard, so treat it as
    -- non-canonical and let the term degrade to an uninterpreted symbol.
    return false

/-- Whether `inst` is accompanied by a `LawfulBEq` proof for `carrier`.

Unlike arithmetic dictionaries, a nonstandard `BEq` can still be translated as
SMT equality when the local context proves that it coincides with propositional
equality. Without this check, `⟨fun _ _ => false⟩ : BEq α` would make `a == a`
translate to the true SMT equation `a = a`. -/
def hasLawfulBEq (carrier inst : Expr) : TranslateM Bool := do
  let carrier ← instantiateMVars carrier
  let some level := (← getLevel carrier).dec | return false
  try
    let _ ← synthInstance (mkApp2 (mkConst ``LawfulBEq [level]) carrier inst)
    return true
  catch _ =>
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
private def legacyDatatypeApp (n : Name) (typeArgs : Array Expr) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | return false
  if iv.numIndices != 0 then return false
  if typeArgs.size != iv.numParams then return false
  if n == ``Nat || n == ``Int || n == ``Bool || n == ``String then return false
  if iv.ctors.isEmpty then return false
  if isClass env n then return false
  for argument in typeArgs do
    let type ← whnf (← inferType argument)
    unless type.isSort do return false
    if (← instantiateMVars argument).hasExprMVar then return false
  unless (match iv.type.getForallBody with
      | .sort level => !level.isZero
      | _ => false) do
    return false
  let fieldsOk ← iv.ctors.allM fun ctorName => do
    let info ← getConstInfoCtor ctorName
    let ctorType ← instantiateForall info.type typeArgs
    forallTelescopeReducing ctorType fun fields _ =>
      fields.allM fun field => do
        let type ← whnf (← inferType field)
        if type.isForall then return false
        if ← isProp type then return false
        return true
  unless fieldsOk do return false
  if ← escapesBlock n iv.all.toArray typeArgs then return false
  return true
where
  escapesBlock (n : Name) (block : Array Name) (typeArgs : Array Expr) :
      MetaM Bool := do
    let inBlock : Std.HashSet Name := block.foldl (·.insert ·) {}
    let some (.inductInfo iv) := (← getEnv).find? n | return false
    iv.ctors.anyM fun ctorName => do
      let info ← getConstInfoCtor ctorName
      let ctorType ← instantiateForall info.type typeArgs
      forallTelescopeReducing ctorType fun fields _ =>
        fields.anyM fun field => do
          let type ← whnf (← inferType field)
          match type.getAppFn with
          | .const member _ => if inBlock.contains member then return false
          | _ => pure ()
          reaches inBlock type 8 inBlock

  reaches (targets : Std.HashSet Name) (type : Expr) (fuel : Nat)
      (visiting : Std.HashSet Name) : MetaM Bool := do
    match fuel with
    | 0 => return false
    | fuel + 1 =>
      let type ← whnf type
      let .const name _ := type.getAppFn | return false
      if targets.contains name then return true
      if visiting.contains name then return false
      let some (.inductInfo info) := (← getEnv).find? name | return false
      if info.numIndices != 0 then return false
      let typeArgs := type.getAppArgs
      if typeArgs.size != info.numParams then return false
      let visiting := visiting.insert name
      info.ctors.anyM fun ctorName => do
        let ctorInfo ← getConstInfoCtor ctorName
        let some ctorType ← (try
            pure (some (← instantiateForall ctorInfo.type typeArgs))
          catch _ => pure none) | pure false
        forallTelescopeReducing ctorType fun fields _ =>
          fields.anyM fun field => do
            reaches targets (← inferType field) fuel visiting

/-- Select legacy or certified datatype acceptance explicitly. The legacy
predicate remains the default so enabling the growing certified fragment cannot
silently perturb existing benchmarks. -/
def isSupportedDatatypeApp (n : Name) (typeArgs : Array Expr)
    (certified := false) : MetaM Bool := do
  if certified then
    return (← Metatheory.Reification.reifyDatatypeApp n typeArgs).isOk
  legacyDatatypeApp n typeArgs

/-- `isSupportedDatatypeApp` for a fully-applied type expression. -/
def supportedDatatypeType? (e : Expr) : TranslateM (Option (Name × Array Expr)) := do
  let e ← whnf e
  let .const n _ := e.getAppFn | return none
  let args := e.getAppArgs
  let certified := (← TranslateM.getConfig).certifyDatatype
  if certified then
    match ← Metatheory.Reification.reifyDatatypeApp n args with
    | .ok _ => return some (n, args)
    | .error reason =>
        if let some (.inductInfo _) := (← getEnv).find? n then
          TranslateM.markDatatypeTrusted reason
        return none
  if ← isSupportedDatatypeApp n args then return some (n, args)
  return none


/-- Whether `ty` is an *uninhabited* Lean type, which SMT cannot model: every SMT
sort is non-empty, so `∀ x : Empty, P` (vacuously true) would translate to the
much stronger `(forall ((x S)) P)`.

Detected structurally: a `Type`-valued inductive with no constructors. `Prop`s are
not affected (they map to `Bool`). -/
def isEmptyType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  let .const n _ := ty.getAppFn | return false
  let some (.inductInfo iv) := (← getEnv).find? n | return false
  if iv.ctors.isEmpty && iv.numIndices == 0 then return true
  if iv.numIndices != 0 || ty.getAppArgs.size != iv.numParams then return false
  let some shape ← Metatheory.Reification.reifyDatatypeShape? n ty.getAppArgs
    | return false
  let some data := shape.find? n | return false
  return (Metatheory.Datatype.seed? shape.block shape.arity data).isNone

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

/-- Allocator-selected names and external sort images for one reified mutual
datatype block. Only sort positions need a size proof; constructor and selector
positions are checked by exact command equality below. -/
structure AllocatedDataNames (arity : Nat) where
  sorts : Array String
  sorts_size : sorts.size = arity
  ctors : Array (Array String)
  sels : Array (Array (Array String))
  bases : List (Metatheory.BaseSort × SSort)

namespace AllocatedDataNames

private def nested? {α : Type} (values : Array (Array α))
    (outer inner : Nat) : Option α := do
  let row ← values[outer]?
  row[inner]?

private def triple? {α : Type} (values : Array (Array (Array α)))
    (first second third : Nat) : Option α := do
  let rows ← values[first]?
  let row ← rows[second]?
  row[third]?

/-- The certified SMT datatype encoding determined by the Crush translator's allocated names. -/
def blockEncoding {arity : Nat} (names : AllocatedDataNames arity) :
    Metatheory.SMT.Datatype.BlockEncoding arity where
  name
    | .sort data => names.sorts[data.val]'(by
        rw [names.sorts_size]
        exact data.isLt)
    | .ctor data ctor =>
        (nested? names.ctors data.val ctor).getD s!"__invalid_ctor_{data.val}_{ctor}"
    | .sel data ctor field =>
        (triple? names.sels data.val ctor field).getD
          s!"__invalid_sel_{data.val}_{ctor}_{field}"
  baseSort := fun sort =>
    (names.bases.find? fun entry => entry.1 == sort).map (·.2) |>.getD
      (.app (.symb sort.name) #[])

end AllocatedDataNames

/-- Build a typed SMT datatype declaration only when it equals the canonical command
computed from the reified datatype block. -/
def buildDatatypeDeclaration? (block : Metatheory.Reification.DatatypeBlock)
    (names : AllocatedDataNames block.arity) :
    Option Metatheory.VCG.DatatypeDeclaration :=
  let encoding := names.blockEncoding
  let command := Metatheory.SMT.Datatype.command block.block encoding
  let sortNames := List.ofFn fun data : Fin block.arity =>
    encoding.name (.sort data)
  let rawSymbols := SMT.datatypeSymbols
    (Metatheory.SMT.Datatype.entries block.block encoding)
  if nameNodup : sortNames.Nodup then
    if sortsFresh : sortNames.all fun name =>
        name != "Bool" && name != "Int" && name != "String" then
      if symbolsNodup : rawSymbols.Nodup then
        if symbolsFresh : rawSymbols.all fun symbol =>
            decide (SMT.NotBuiltin symbol) then
          some {
            reifiedBlock := block
            typed := {
              blockEncoding := encoding
              command
              command_eq := rfl
              wf := {
                blockWF := block.wf
                names := Metatheory.SMT.Datatype.BlockEncoding.wf_of_names
                  encoding nameNodup
                sorts_fresh := by
                  intro data
                  have member : encoding.name (.sort data) ∈ sortNames := by
                    exact List.mem_ofFn.mpr ⟨data, rfl⟩
                  have checked := List.all_eq_true.mp sortsFresh _ member
                  simp only [bne_iff_ne, Bool.and_eq_true] at checked
                  rcases checked with ⟨⟨notBool, notInt⟩, notString⟩
                  constructor
                  · intro equal
                    injection equal with identEqual
                    injection identEqual with nameEqual
                    exact notBool nameEqual
                  · constructor
                    · intro equal
                      injection equal with identEqual
                      injection identEqual with nameEqual
                      exact notInt nameEqual
                    · intro equal
                      injection equal with identEqual
                      injection identEqual with nameEqual
                      exact notString nameEqual
                symbols := symbolsNodup
                symbols_fresh := by
                  intro symbol member
                  have checked := List.all_eq_true.mp symbolsFresh symbol member
                  exact of_decide_eq_true checked } } }
        else none
      else none
    else none
  else none

/-- One constructor discovered before datatype allocation mutates translation
state. Field types are ground because both legacy and certified acceptance pass
through `reifyDatatypeBlock?`. -/
structure DataCtorPlan where
  name : Name
  fields : Array Expr

/-- One member of a mutual datatype declaration plan. -/
structure DataMemberPlan where
  name : Name
  ctors : Array DataCtorPlan

/-- Read-only Lean declaration information consumed by `declareDatatype`.
Separating this discovery value from allocation and emission prevents later
state changes from affecting which constructors or fields are traversed. -/
structure DatatypePlan where
  head : Name
  typeArgs : Array Expr
  members : Array DataMemberPlan

/-- Discover the complete mutual block without allocating names or emitting SMT
commands. Accepted datatypes have nondependent ground fields, so their types can
leave the temporary constructor telescope safely. -/
partial def datatypePlan (head : Name) (typeArgs : Array Expr) :
    MetaM DatatypePlan := do
  let info ← getConstInfoInduct head
  let mut members : Array DataMemberPlan := #[]
  for name in info.all do
    let memberInfo ← getConstInfoInduct name
    let mut ctors : Array DataCtorPlan := #[]
    for ctorName in memberInfo.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorType ← instantiateForall ctorInfo.type typeArgs
      let fields ← forallTelescopeReducing ctorType fun args _ => do
        let mut fields : Array Expr := #[]
        for field in args do
          let type ← instantiateMVars (← inferType field)
          if args.any fun argument => type.containsFVar argument.fvarId! then
            throwError "crush: datatype plan found dependent field in `{ctorName}`"
          fields := fields.push type
        return fields
      ctors := ctors.push { name := ctorName, fields }
    members := members.push { name, ctors }
  return { head, typeArgs, members }

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
  types     : Array Expr := #[]
  instances : Array Expr := #[]

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
  for arg in args do
    let fnTypeWhnf ← whnf fnType
    let binderInfo? :=
      match fnTypeWhnf with
      | .forallE _ _ _ binderInfo => some binderInfo
      | _ => none
    let argType ← inferType arg
    if ← isProp argType then
      pure ()
    else if (← whnf argType).isSort then
      out := { out with types := out.types.push arg }
    else if binderInfo? == some .instImplicit then
      let dependsOnBound :=
        (Lean.collectFVars {} arg).fvarIds.any boundVars.contains
      if dependsOnBound then
        out := { out with values := out.values.push arg }
      else
        out := { out with instances := out.instances.push arg }
    else
      out := { out with values := out.values.push arg }
    applied := mkApp applied arg
    fnType ←
      match fnTypeWhnf with
      | .forallE _ _ body _ => pure (body.instantiate1 arg)
      | _ => inferType applied
  return out

/-- Pure SMT syntax corresponding to the verified metatheory's
`Guarded.natInt.guard`.  Keeping this constructor named minimizes the refinement
boundary between `Expr` recognition and the guarded semantic proof. -/
def natNonnegativeGuard (term : SMT.Term) : SMT.Term :=
  (smt| (>= $term 0))

/-- Pure guard combination used by quantified binders.  Its two branches are
the syntax counterparts of `Encoding.guardedForall` and
`Encoding.guardedExists`. -/
def guardedQuantifierBody (isForall : Bool) (condition body : SMT.Term) : SMT.Term :=
  if isForall then (smt| (=> $condition $body))
  else (smt| (and $condition $body))

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
    if let some s ← trySortHandlers handlers e then
      TranslateM.markTrusted (.sortHandler e)
      return s
    let normalized ← whnf e
    if normalized != e then
      if let some s ← trySortHandlers handlers normalized then
        TranslateM.markTrusted (.sortHandler normalized)
        return s
    let e := normalized
    match e with
    | .const ``Bool _ => return boolSort
    | .const ``Nat _  => return intSort
    | .const ``Int _  => return intSort
    | .const ``String _ => return stringSort
    -- `Prop` is the sort of propositions and maps to SMT `Bool`. A *larger* universe
    -- does not: mapping `Type` to `Bool` would put every Lean type into a
    -- two-element set, so three distinct types would have to collide and the solver
    -- could "prove" type equalities that are false. Such a position gets an opaque
    -- sort instead, which is uninterpreted and therefore sound.
    | .sort l => if l.isZero then return boolSort
                 else declareUninterpretedSort e
    | _ =>
    -- Lean arrays are finite sequences, not their implementation-level `List`
    -- structure. Represent them by a length plus an SMT theory array so reads and
    -- writes receive native read-over-write semantics.
    if let some elem ← finiteArrayElem? e then
      let enc ← declareFiniteArray elem
      return .app (.symb enc.sortName) #[]
    -- `BitVec w` at a statically-known width maps to the indexed sort
    -- `(_ BitVec w)`. A symbolic width has no SMT counterpart, so it falls through
    -- to an opaque sort (where `BitVec` ops will not be recognized either).
    match ← bvWidthOfType? e with
    | some w => return bitvecSort w
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
  intermediate closure.

  The `app` result carries the codomain's well-formedness constraint at well-formed
  arguments — the arrow-sort counterpart of `emitResultWF`, confining `app f n` for a
  `Nat`-codomain arrow to the nonnegative `Int`s. -/
  partial def declareArrowSort (ty : Expr) : TranslateM (SSort × String) := do
    let some shape ← arrowShape? ty
      | throwError "crush: internal — `declareArrowSort` on a non-arrow {ty}"
    -- The witness determines the declaration telescope. Symbol identity remains
    -- keyed by the caller's expression: changing that identity to `whnf ty`
    -- requires a separate stability theorem for metavariables and transparency.
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
      -- `app` takes the function value plus the flattened argument sorts.
      let ⟨argumentImages, argumentTypesEq⟩ ←
        Metatheory.VCG.mapSortImagesM
          (fun reified => emitSort reified.expr) shape.flatten.1
      let resultType := shape.flatten.2
      let resultImage : Metatheory.VCG.SortImage :=
        { reified := resultType, smt := ← emitSort resultType.expr }
      let argSorts := (argumentImages.map (·.smt)).toArray
      let resSort := resultImage.smt
      let appCommand := appDeclaration appName sort argSorts resSort
      TranslateM.emitAllocatedCommand (.app {
        arrow := shape
        name := appName
        functionSort := sort
        arguments := argumentImages
        result := resultImage
        argumentTypes_eq := argumentTypesEq
        resultType_eq := rfl
        command := appCommand
        command_eq := rfl })
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
        let binders := #[(fName, sort)] ++ names.zip argSorts
        TranslateM.emitCommand (.assert (.forallE binders guarded))
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
    -- Agreement is required only at well-formed arguments, which is what makes
    -- `∀ x : Nat, f x = g x ⊢ f = g` provable: the binders range over `Int`, where the
    -- two `Nat` functions need not agree.
    let pointwise := (smt| (= $appA $appB))
    let pointwise ←
      match ← binderGuard (binders.map (·.1)) shape.args with
      | none => pure pointwise
      | some g => pure (smt| (=> $g $pointwise))
    let premise := SMT.Term.forallE binders pointwise
    let aRef := SMT.Term.const a
    let bRef := SMT.Term.const b
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
    let captures := selectClosureCaptures lam fun fid =>
      st.boundVars.contains fid || st.funVars.contains fid
    let replayHead ← mkLambdaFVars (captures.map mkFVar) lam
    if let some existing ← TranslateM.structuralSymbol? key then
      TranslateM.recordSymbolExpr existing replayHead
      -- Already declared: rebuild the application from the recorded captures.
      let capArgs ← captures.mapM fun fid => emitTerm (.fvar fid)
      return if capArgs.isEmpty then .const existing
             else .app (.symb existing) capArgs
    let cloName ← TranslateM.symbolForStructural key "clo"
    TranslateM.recordSymbolExpr cloName replayHead
    -- Retain the same reified types used by `ClosureCaptureCertificate` and its
    -- `closureDecl_args` theorem. `preserveExpr` keeps the Crush translator's existing
    -- sort-dispatch identity while the reified value supplies the typed source index.
    let certifiedClosure? ← Metatheory.Reification.certifyLocalClosure? lam captures
    let evidence : Metatheory.VCG.ClosureEvidence ←
      match certifiedClosure? with
      | some certified => pure (.proved certified)
      | none => do
          let reason := Metatheory.VCG.TrustReason.closure lam
          TranslateM.markTrusted reason
          pure (.trusted reason)
    let captureTypes ←
      match certifiedClosure? with
      | some certified => pure certified.captureTypes
      | none => captures.mapM fun fid => do
          Metatheory.Reification.reifyType (← fid.getType) (preserveExpr := true)
    let ⟨captureImages, captureTypesEq⟩ ←
      Metatheory.VCG.mapSortImagesM
        (fun reified => emitSort reified.expr) captureTypes.toList
    let capSorts := (captureImages.map (·.smt)).toArray
    let (arrowSort, _) ← declareArrowSort lamTy
    let closureCommand := closureDeclaration cloName capSorts arrowSort
    TranslateM.emitAllocatedCommand (.closure {
      arrow := shape
      name := cloName
      captures := captureImages
      captureTypes := captureTypes.toList
      captureTypes_eq := captureTypesEq
      functionSort := arrowSort
      command := closureCommand
      command_eq := rfl })
    markFunDeclared cloName
    -- The defining axiom. Fresh SMT variables for the λ's own parameters; the
    -- captures are quantified too so the axiom holds for every instantiation.
    let mut binders : Array (String × SSort) := #[]
    let mut capRefs : Array SMT.Term := #[]
    for (fid, captureType) in captures.zip captureTypes do
      let nm := (st.boundVars.get? fid).getD ((st.funVars.get? fid).getD "c")
      binders := binders.push (nm, ← emitSort captureType.expr)
      capRefs := capRefs.push (.const nm)
    let cloApp := if capRefs.isEmpty then SMT.Term.const cloName
                  else SMT.Term.app (.symb cloName) capRefs
    -- Enter the λ's binders with real fvars so the body becomes closed.
    let (paramBinders, bodyTerm) ← emitLambdaBody lam shape
    let parameterRefs := paramBinders.map (fun (n, _) => SMT.Term.const n)
    let rawEquation := closureEquation appName cloApp parameterRefs bodyTerm
    -- The defining equation holds at well-formed arguments and captures only; the body is
    -- a Lean term and has no meaning at a value outside the encoded type's image.
    let captureTys := captureTypes.map Metatheory.Reification.ReifiedType.expr
    let guard ← binderGuard ((binders ++ paramBinders).map (·.1))
      (captureTys ++ shape.args)
    let axiomBody :=
      match guard with
      | none => rawEquation
      | some g => SMT.Term.symbApp "=>" #[g, rawEquation]
    let allBinders := binders ++ paramBinders
    let equationCommand := closureEquationCommand allBinders axiomBody
    TranslateM.emitAllocatedCommand (.closureEquation {
      arrow := shape
      appName
      closure := cloApp
      parameters := parameterRefs
      body := bodyTerm
      rawEquation
      rawEquation_eq := rfl
      guard
      guardedEquation := axiomBody
      guardedEquation_eq := rfl
      binders := allBinders
      evidence
      command := equationCommand
      command_eq := rfl })
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

  /-- Emit a `declare-sort` for an opaque type, once. -/
  partial def declareUninterpretedSort (e : Expr) : TranslateM SSort := do
    let key : StructuralKey := { tag := "opaque-sort", typeExprs := #[e] }
    let hint := match e with | .const n _ => nameHint n | _ => "s"
    let name ← TranslateM.symbolForStructural key hint
    -- Remember the Lean type behind the sort, so proof replay can give a quantifier
    -- binder over this sort its Lean type back (`AletheTerm.sortToType?`).
    TranslateM.recordSymbolExpr name e
    if !(← declaredSort name) then
      TranslateM.emitCommand (.declSort name 0)
      markSortDeclared name
    return .app (.symb name) #[]

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
    let intSort := SMT.intSort
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
        SMT.boolSort body)
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
  partial def declareDatatype (n : Name) (typeArgs : Array Expr := #[]) :
      TranslateM String := do
    -- Key structurally on the head and its instantiation, so `Option Int` and
    -- `Option Bool` get distinct sorts, constructors, and selectors.
    let key : StructuralKey := { tag := "datatype", name := n, typeExprs := typeArgs }
    if let some name ← TranslateM.structuralSymbol? key then
      return name
    let certify := (← TranslateM.getConfig).certifyDatatype
    let certifiedBlock? : Option Metatheory.Reification.DatatypeBlock ←
      if certify then
        match (← get).activeDataSignature with
        | some (.pack env _) =>
            let some found ← env.find? n typeArgs
              | throwError "crush: active datatype environment omitted `{n}`"
            pure (some found.block)
        | none =>
            match ← Metatheory.Reification.reifyDatatypeApp n typeArgs with
            | .ok accepted => pure (some accepted.block)
            | .error reason =>
                throwError "crush: certified datatype acceptance drift for `{n}`: \
                  {repr reason}"
      else
        pure none
    let plan ← datatypePlan n typeArgs
    -- Emit the whole mutual block together: SMT-LIB requires mutually-recursive
    -- datatypes in one `declare-datatypes` (`tree`'s selector range `treelist` must
    -- be in scope when `tree` is), and a member's `wf` axiom may reference a sibling's
    -- `wf`. `iv.all` is a singleton for an ordinary inductive, so that path is
    -- unchanged; a mutual block shares parameters, so the same structural
    -- arguments key every member.
    -- Reserve every member's sort name first, so a field mentioning a sibling resolves
    -- to it via the idempotent early-return above rather than recursing.
    let mut memberSorts : Array (Name × String) := #[]
    let mut sortNames : Array String := #[]
    for member in plan.members do
      let memberKey : StructuralKey := {
        tag := "datatype", name := member.name, typeExprs := typeArgs
      }
      let mSort ← TranslateM.symbolForStructural memberKey (nameHint member.name)
      markSortDeclared mSort
      memberSorts := memberSorts.push (member.name, mSort)
      sortNames := sortNames.push mSort
    let mut dtInfos : Array (String × Nat × DatatypeDecl) := #[]
    let mut memberWF : Array (String × Array (String × Array (String × Expr))) := #[]
    let mut ctorNames : Array (Array String) := #[]
    let mut selNames : Array (Array (Array String)) := #[]
    let mut baseSorts : List (Metatheory.BaseSort × SSort) := []
    for (member, named) in plan.members.zip memberSorts do
      let (m, mSort) := named
      let mut ctorDecls : Array CtorDecl := #[]
      let mut memberCtors : Array String := #[]
      let mut memberSels : Array (Array String) := #[]
      -- Field descriptors for the wf axiom: per ctor, the selectors needing a guard.
      let mut wfParts : Array (String × Array (String × Expr)) := #[]
      for ctor in member.ctors do
        let ctorSym ← reserveCtorSymbol mSort ctor.name
        memberCtors := memberCtors.push ctorSym
        let mut selDecls : Array (String × SSort) := #[]
        let mut allocatedSels : Array String := #[]
        let mut guards : Array (String × Expr) := #[]
        let mut ctorBases : List (Metatheory.BaseSort × SSort) := []
        for i in [0:ctor.fields.size] do
          let fieldTy := ctor.fields[i]!
          let s ← emitSort fieldTy
          let selName ← reserveSelSymbol mSort ctor.name i
          selDecls := selDecls.push (selName, s)
          allocatedSels := allocatedSels.push selName
          match ← Metatheory.Reification.reifyType fieldTy with
          | .base _ base =>
              unless ctorBases.any fun entry => entry.1 == base do
                ctorBases := (base, s) :: ctorBases
          | .bool _ | .arrow .. => pure ()
          if (← needsWFGuard fieldTy) then
            guards := guards.push (selName, fieldTy)
        for entry in ctorBases do
          unless baseSorts.any fun found => found.1 == entry.1 do
            baseSorts := entry :: baseSorts
        memberSels := memberSels.push allocatedSels
        ctorDecls := ctorDecls.push { name := ctorSym, selDecls }
        wfParts := wfParts.push (ctorSym, guards)
      dtInfos := dtInfos.push (mSort, 0, { ctors := ctorDecls })
      memberWF := memberWF.push (mSort, wfParts)
      ctorNames := ctorNames.push memberCtors
      selNames := selNames.push memberSels
    if let some block := certifiedBlock? then
      if sizeEq : sortNames.size = block.arity then
        let names : AllocatedDataNames block.arity := {
          sorts := sortNames
          sorts_size := sizeEq
          ctors := ctorNames
          sels := selNames
          bases := baseSorts }
        let some declaration := buildDatatypeDeclaration? block names
          | throwError "crush: allocated SMT datatype declaration for `{n}` disagrees with its block"
        let _ ← TranslateM.emitDatatypeDeclaration declaration
      else
        throwError "crush: certified mutual block size drift for `{n}`"
    else
      TranslateM.emitCommand (.declDatatypes dtInfos)
    -- Reserve all predicates before building any body, then define the whole mutual
    -- block with `define-funs-rec`. Quantified equations for recursive predicates make
    -- solvers return `unknown` even on unrelated ground queries.
    let mut needDef : Array (String × Array (String × Array (String × Expr))) := #[]
    for (mSort, wfParts) in memberWF do
      if ← declDatatypeWF mSort then
        needDef := needDef.push (mSort, wfParts)
    let mut wfDefs : Array FunDef := #[]
    for (mSort, wfParts) in needDef do
      wfDefs := wfDefs.push (← datatypeWFDef mSort wfParts)
    unless wfDefs.isEmpty do
      let command := SMT.Command.defFunsRec wfDefs
      if let some reifiedBlock := certifiedBlock? then
        TranslateM.emitAllocatedCommand (.datatypeGuard {
          reifiedBlock
          definitions := wfDefs
          command
          command_eq := rfl })
      else
        TranslateM.emitCommand command
    let some (_, nSort) := memberSorts.find? (·.1 == plan.head)
      | throwError "crush: internal — `{n}` missing from its own mutual block"
    return nSort

  /-- Whether values of `ty` occupy a *proper subset* of their SMT sort, so a
  quantifier over them needs a guard. True for `Nat` (encoded as `Int`) and for any
  datatype that transitively contains such a field.

  `visiting` holds the datatype heads already on the stack. A recursive datatype needs a
  guard iff some field does, so re-entering one contributes nothing new and returns
  `false` — which is also what makes this terminate. Tracking a *set* rather than just
  comparing against the current head is essential: recursion through another type
  (`Rose` ⊃ `List Rose` ⊃ `Rose`) never repeats two heads in a row, so a
  self-reference-only check recurses forever and overflows the stack. -/
  partial def needsWFGuard (ty : Expr) (visiting : Std.HashSet Name := {}) :
      TranslateM Bool := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then return true
    if let some elem ← finiteArrayElem? ty then
      return ← finiteArraySortSelected ty elem
    let some (n, typeArgs) ← supportedDatatypeType? ty | return false
    if visiting.contains n then return false
    let visiting := visiting.insert n
    -- Fields are examined at this instantiation, so a `Nat` reached only through the type
    -- parameter (`Option Nat`) is caught, while `Option Int` is not.
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
    if ← declaredFun wf then return false
    markFunDeclared wf
    return true

  /-- Build one member of a mutually recursive well-formedness definition. -/
  partial def datatypeWFDef (sortName : String)
      (parts : Array (String × Array (String × Expr))) : TranslateM FunDef := do
    let wf ← reserveWfSymbol sortName
    let sort := SSort.app (.symb sortName) #[]
    let v ← TranslateM.freshSymbol "d"
    -- Bodies in the raw syntax refer to the local argument by de Bruijn index.
    let x := SMT.Term.bvar 0
    let mut encoded : Array (String × Array SMT.Term) := #[]
    for (ctorSym, guards) in parts do
      let mut fieldConds : Array SMT.Term := #[]
      for (selName, fieldTy) in guards do
        let selApp := SMT.Term.app (.symb selName) #[x]
        if let some c ← wfCondition fieldTy selApp then
          fieldConds := fieldConds.push c
      encoded := encoded.push (ctorSym, fieldConds)
    return wfDef wf v sort encoded

  /-- The well-formedness condition on an SMT term of Lean type `ty`: `≥ 0` for
  `Nat`, `wf_T` for a guarded datatype, `none` when nothing is needed. -/
  partial def wfCondition (ty : Expr) (t : SMT.Term) : TranslateM (Option SMT.Term) := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then
      return some (natNonnegativeGuard t)
    if let some elem ← finiteArrayElem? ty then
      unless ← finiteArraySortSelected ty elem do return none
      let enc ← declareFiniteArray elem
      let wf ← reserveWfSymbol enc.sortName
      return some (.app (.symb wf) #[t])
    let some (n, typeArgs) ← supportedDatatypeType? ty | return none
    if !(← needsWFGuard ty) then return none
    let sortName ← declareDatatype n typeArgs
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
    let e ← instantiateMVars e
    TranslateM.markDirect e
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
          TranslateM.markTrusted (.termHandler e)
          return t
    -- Head-indexed lowerings are the efficient extension path for one specific
    -- constant. General handlers above retain first refusal so existing user
    -- overrides continue to supersede built-in lowerings.
    let (fn, args) := getAppFnArgs' e
    if let .const head _ := fn then
      if ← hasCertifiedDef head then
        let ctx : TranslationCtx := {
          fn, args
          emitTerm := emitTerm
          emitSort := emitSort
          declare  := declareViaThunk }
        let some result ← CertifiedPrimitiveMapping.lowerDef head ctx
          | throwError "crush: `@[crush_certified_def]` could not reduce `{head}` at \
              this application. For symbolic recursion, register its proved equations \
              with `@[crush_unfold]` or `@[crush_defeq]` instead."
        return result
      if ← hasCertifiedLoweringsFor head then
        let ctx : TranslationCtx := {
          fn, args
          emitTerm := emitTerm
          emitSort := emitSort
          declare  := declareViaThunk }
        for mapping in (← getCertifiedLoweringsFor head) do
          if let some result ← mapping.lower ctx then
            if let some targetSymbol := result.targetSymbol? then
              TranslateM.recordCertifiedHookUse mapping.declaration targetSymbol
            return result.term
      if ← hasLoweringsFor head then
        let ctx : TranslationCtx := {
          fn, args
          emitTerm := emitTerm
          emitSort := emitSort
          declare  := declareViaThunk }
        for lowering in (← getLoweringsFor head) do
          if let some t ← lowering ctx then
            TranslateM.markTrusted (.lowering head)
            return t
    -- Result-indexed lowerings cover terms whose application head is unstable.
    -- Direct type heads are cheap; only syntactic function types require opening
    -- binders. Named aliases remain separate keys by design.
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
              TranslateM.markTrusted (.resultLowering resultHead)
              return t
    let logicalClassProjection ← isLogicalClassProjection fn
    -- A logical class field may itself return a predicate/relation before all
    -- ordinary arguments are supplied (`Membership.mem inst : α → γ → Prop`).
    -- Expose the selected instance before the generic HO encoder materializes
    -- that partial application as an unrelated function value.
    if logicalClassProjection && (← whnf (← inferType e)).isArrow then
      let reduced ← withTransparency .instances <| whnf e
      if reduced != e then
        return ← emitTerm reduced
    -- Higher-order forms, before the first-order structural path.
    if let some t ← hoTerm? e then
      return t
    -- Fast path for the structural logical/theory core.
    match ← structural? e with
    | some t => return t
    | none =>
      -- A constructor of a supported datatype → the SMT constructor symbol.
      if let some t ← ctorApp? fn args then
        return t
      -- A structure projection → the SMT selector.
      if let some t ← projApp? fn args then
        return t
      -- Concrete logical fields should expose the selected instance's semantics.
      -- The declaration-based check above excludes polymorphic data projections
      -- that merely happen to be instantiated at `Bool`.
      if logicalClassProjection then
        let reduced ← withTransparency .instances <| whnf e
        if reduced != e then
          return ← emitTerm reduced
      if let .const head _ := fn then
        -- A nullary transparent definition is a value alias, not a fresh SMT
        -- constant. The nullary restriction avoids unfolding recursive or
        -- data-processing definitions that have dedicated lowerings.
        if args.isEmpty then
          if ← Lean.isReducible head then
            let reduced ← withReducible <| whnf e
            if reduced != e then
              return ← emitTerm reduced
          else if ← Lean.isImplicitReducible head then
            let reduced ← withTransparency .instances <| whnf e
            if reduced != e then
              return ← emitTerm reduced
      -- Default: uninterpreted function/atom applied to translated args.
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
    -- (1) A λ becomes a closure with a defining axiom (or a native `lambda`).
    if e.isLambda then
      -- Dependent function values such as `DecidableEq α` have no first-order
      -- arrow sort: their result sort mentions an argument. Keep those as opaque
      -- atoms rather than entering `declareArrowSort`, which only accepts a
      -- non-dependent `ArrowShape`.
      if (← arrowShape? (← inferType e)).isSome then
        if mode == .native then
          TranslateM.markTrusted (.nativeHO e)
          return some (← emitNativeLambda e)
        return some (← emitClosure e)
      return none
    -- (2) Any expression whose result is still a function is a function *value*.
    -- Materialize it now so a later use cannot declare the partial application as
    -- an unrelated first-order symbol.
    if (← whnf (← inferType e)).isArrow then
      return some (← emitFunValue e)
    -- (3) An application whose head is a function-typed *bound variable* must route
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
        -- Partial application: `app` is n-ary over the *fully flattened* arg list, so
        -- fewer args than that arity (`x (y f)`, result still a function) would emit
        -- `app` under-applied — ill-sorted, and the result is a function value. Emit
        -- it as a closure of the residual arrow sort instead. (Native mode applies
        -- functions directly, so partial application is fine there.)
        if mode != .native then
          if let some shape ← arrowShape? (← whnf (← fid.getType)) then
            if args.size < shape.args.size then
              return some (← emitFunValue e)
        let sargs ← args.mapM emitTerm
        -- In native mode the variable *is* a function: apply it directly.
        if mode == .native then
          TranslateM.markTrusted (.nativeHO e)
          return some (.app (.symb vname) sargs)
        return some (.app (.symb appSym) (#[.const vname] ++ sargs))
    -- (4) A non-symbol head (`(if c then f else g) x`, a projection, a let, ...)
    -- is itself a value of an arrow sort. Apply that value through the arrow sort's
    -- `app` symbol rather than inventing a first-order declaration for its syntax.
    unless args.isEmpty do
      unless fn.isConst || fn.isFVar do
        if let some shape ← arrowShape? (← inferType fn) then
          if args.size == shape.args.size then
            let sfn ← emitFunValue fn
            let sargs ← args.mapM emitTerm
            if mode == .native then
              TranslateM.markTrusted (.nativeHO e)
              -- SMT-LIB application syntax requires an identifier in head position.
              -- A local `let` gives an arbitrary function value such a name.
              let name ← TranslateM.freshSymbol "hof"
              return some (.letE #[(name, sfn)] (.app (.symb name) sargs))
            let (_, appSym) ← declareArrowSort (← inferType fn)
            return some (.app (.symb appSym) (#[sfn] ++ sargs))
    -- (5) An equation between function-typed terms needs extensionality to be
    -- provable, and needs both sides encoded as `Fn` values rather than symbols.
    match_expr e with
    | Eq ty a b =>
      if (← whnf ty).isArrow then
        -- Native mode gets extensionality from the solver itself; the encoded modes
        -- need it asserted explicitly (verified load-bearing).
        if mode != .native then
          emitExtensionality ty
        else
          TranslateM.markTrusted (.nativeHO e)
        return some (smt| (= $(← emitFunValue a) $(← emitFunValue b)))
      return none
    | _ => return none

  /-- A native higher-order `lambda` term, for HO-capable backends. -/
  partial def emitNativeLambda (lam : Expr) : TranslateM SMT.Term := do
    TranslateM.markTrusted (.nativeHO lam)
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
    if mode == .native then
      TranslateM.markTrusted (.nativeHO e)
    if e.isLambda then
      return ← if mode == .native then emitNativeLambda e else emitClosure e
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- Function-valued conditionals are values in the arrow sort just like scalar
    -- conditionals. Handling them directly is what makes
    -- `(if c then f else g) x` terminate instead of recursively η-expanding the
    -- same head while constructing its closure equation.
    match_expr e with
    | ite _ c _ a b =>
      return (smt| (ite $(← emitTerm c) $(← emitFunValue a) $(← emitFunValue b)))
    | cond _ c a b =>
      return (smt| (ite $(← emitTerm c) $(← emitFunValue a) $(← emitFunValue b)))
    | _ => pure ()
    -- Let-bound function expressions reduce without losing semantics. Do this
    -- narrowly for a syntactic let rather than unfolding arbitrary definitions.
    if e.isLet then
      let reduced ← whnf e
      if reduced != e then return ← emitFunValue reduced
    -- A function-valued projection/atom can directly inhabit the arrow sort.
    -- Applications of the same expression will route through `app`, preserving
    -- identity without pretending the value is a first-order function symbol.
    if e.isProj then
      return ← defaultApp e #[]
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
    if (← TranslateM.getConfig).certifyDatatype then
      if let some (.pack data _) := (← get).activeDataSignature then
        let some app ← data.projApp? (mkAppN fn args) | return none
        let sortName ← declareDatatype app.ctorName.getPrefix app.typeArgs
        let sel ← reserveSelSymbol sortName app.ctorName app.fieldIndex
        let target ← emitTerm app.target
        return some (.app (.symb sel) #[target])
    let .const pn _ := fn | return none
    let some info ← getProjectionFnInfo? pn | return none
    -- Projections take the structure as the argument after `info.numParams`.
    let some structArg := args[info.numParams]? | return none
    let structTy ← whnf (← inferType structArg)
    if (← finiteArrayElem? structTy).isSome then return none
    let some (_, typeArgs) ← supportedDatatypeType? structTy | return none
    let sortName ← declareDatatype info.ctorName.getPrefix typeArgs
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
    if (← TranslateM.getConfig).certifyDatatype then
      if let some (.pack data _) := (← get).activeDataSignature then
        let some app ← data.ctorApp? (mkAppN fn args) | return none
        let sortName ← declareDatatype app.induct app.typeArgs
        let values ← app.values.mapM emitTerm
        let ctor ← reserveCtorSymbol sortName app.name
        return some (.app (.symb ctor) values)
    let .const cn _ := fn | return none
    let env ← getEnv
    let some (.ctorInfo ci) := env.find? cn | return none
    -- The applied constructor's result type carries the instantiation.
    let resTy ← whnf (← inferType (mkAppN fn args))
    if (← finiteArrayElem? resTy).isSome then return none
    let some (_, typeArgs) ← supportedDatatypeType? resTy | return none
    let sortName ← declareDatatype ci.induct typeArgs
    -- Drop the leading type-parameter arguments; keep the value fields.
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
    -- Every recognizer below that matches an overloaded operator
    -- (`HAdd.hAdd`, `LE.le`, `max`, …) assumes the *standard* instance. A
    -- user-supplied instance makes the operator mean something else entirely —
    -- `⟨fun _ _ => 99⟩ : HAdd Int Int Int` is legal, and then `1 + 2 = 99` — so
    -- translating it as SMT `+` proves false goals. Bail out to the uninterpreted
    -- path when the instance is not the one synthesis would choose.
    if ← isNonCanonicalOverload e then return none
    match e with
    | _ =>
    -- Bit-vectors need type-directed dispatch. Library-level String operations
    -- use the public head-indexed lowerings in `DefaultLowerings.lean`.
    match ← bitvecTerm? e with
    | some t => return some t
    | none =>
    -- Only `Nat` and `Int` inhabit the SMT integer theory. Canonical overloaded
    -- instances on every other carrier remain ordinary Lean functions and must
    -- fall through to `defaultApp`; emitting `+`, `<`, `max`, etc. for an opaque
    -- sort produces an ill-sorted SMT script.
    if let some carriers := integerOverloadCarriers? e then
      unless ← isHomogeneousIntegerCarrier carriers do return none
    -- Numeric literals: `@OfNat.ofNat _ n _` and negation.
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      -- A numeral is an SMT literal only at the arithmetic sorts `Nat`/`Int`. At any
      -- other carrier `@OfNat.ofNat T k inst` is sugar for a `T`-value — `(0 :
      -- SignType)` is the constructor `SignType.zero` — so emitting `0` would clash
      -- sorts (z3: "Sorts … incompatible"). Reduce and re-emit through the datatype/
      -- uninterpreted path instead. (Can't just `whnf` unconditionally: `Nat`/`Int`
      -- are theory sorts whose whnf forms have no first-order translation.)
      let ty ← whnf (← inferType e)
      if ty.isConstOf ``Nat || ty.isConstOf ``Int then
        return (← getNatLit? e).map (.lit <| .num ·)
      else
        let e' ← whnf e
        -- A symbolic instance that won't reduce has no value to expose; leave it.
        if e' == e then return none else return some (← emitTerm e')
    | Neg.neg _ _ a =>
      return some (smt| (- $(← emitTerm a)))
    | HDiv.hDiv _ _ _ _ a b =>
      -- SMT-LIB leaves `(div x 0)` to the model while Lean pins it to `0`; pin it
      -- too so the encoding is exact (see `intDivGuard`).
      return some (intDivGuard "div" (← emitTerm a) (← emitTerm b))
    | HMod.hMod _ _ _ _ a b =>
      return some (intDivGuard "mod" (← emitTerm a) (← emitTerm b))
    | _ =>
    match_expr e with
    | And a b => return some (smt| (and $(← emitTerm a) $(← emitTerm b)))
    | Or a b  => return some (smt| (or $(← emitTerm a) $(← emitTerm b)))
    | Not a   => return some (smt| (not $(← emitTerm a)))
    -- The `Bool`-valued connectives, which are ordinary functions (`not`/`and`/…)
    -- rather than the `Prop` classes above. Since `Prop` and `Bool` share the SMT
    -- `Bool` sort, they map to the same operators — but they are distinct `Expr`s
    -- and must each be recognized, or they become uninterpreted symbols.
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
      -- `Nat` subtraction truncates at 0: `a - b = if a >= b then a - b else 0`.
      -- Encoding it as plain SMT `-` (which can go negative) is unsound.
      let sa ← emitTerm a
      let sb ← emitTerm b
      if (← isNatTyped e) then
        return some (smt| (ite (>= $sa $sb) (- $sa $sb) 0))
      else
        return some (smt| (- $sa $sb))
    -- SMT-LIB has no `max`/`min`, so they expand to an `ite`. Both are translated
    -- for whatever ordered sort the arguments have, so the `Nat` guard and the
    -- `BitVec` dispatch above still apply to the operands.
    | max _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (smt| (ite (>= $sa $sb) $sa $sb))
    | min _ _ a b =>
      let sa ← emitTerm a; let sb ← emitTerm b
      return some (smt| (ite (<= $sa $sb) $sa $sb))
    -- `Nat.succ n` is `n + 1`; it appears from literals and from recursors.
    | Nat.succ a => return some (smt| (+ $(← emitTerm a) 1))
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
    | LE.le _ _ a b => return some (smt| (<= $(← emitTerm a) $(← emitTerm b)))
    | LT.lt _ _ a b => return some (smt| (< $(← emitTerm a) $(← emitTerm b)))
    | GE.ge _ _ a b => return some (smt| (>= $(← emitTerm a) $(← emitTerm b)))
    | GT.gt _ _ a b => return some (smt| (> $(← emitTerm a) $(← emitTerm b)))
    | ite _ c _ a b =>
      -- `if c then a else b`; the condition `c : Prop` becomes an SMT Bool term.
      return some (smt| (ite $(← emitTerm c) $(← emitTerm a) $(← emitTerm b)))
    | cond _ b t e =>
      -- `Bool.cond`/`cond` with a `Bool` scrutinee.
      return some (smt| (ite $(← emitTerm b) $(← emitTerm t) $(← emitTerm e)))
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
            return some (smt| (=> $a $b))
          let b ← emitTerm body
          return some (smt| (=> $a $b))
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
    | Complement.complement _ _ a => return some (smt| (bvnot $(← emitTerm a)))
    | Neg.neg _ _ a => return some (smt| (bvneg $(← emitTerm a)))
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
    | BitVec.zeroExtend _ target x =>
      -- `zeroExtend` is definitionally `setWidth` (both `{w} → (v) → BitVec w →
      -- BitVec v`), but it is a *distinct* declaration, so the `setWidth` arm above
      -- does not fire on it and it would otherwise fall through to an uninterpreted
      -- symbol. Same unsigned resize.
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize false xw tv (← emitTerm x))
    | BitVec.signExtend _ target x =>
      let some tv ← natValue? target | return none
      let some xw ← bvWidthOf? x | return none
      return some (bvResize true xw tv (← emitTerm x))
    | BitVec.extractLsb _ hi lo x =>
      -- The `hi lo` (inclusive high/low bit) form. `extractLsb hi lo` is
      -- `extractLsb' lo (hi + 1 - lo)`; reduce to the `extractLsb'` treatment below
      -- by computing the length. When `hi < lo` the length is zero (empty slice),
      -- which SMT `extract` cannot express, so fall through to opaque.
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
      -- `a ++ b` puts `a` in the high bits, matching SMT `concat` (verified:
      -- `(4 : BitVec 8) ++ (5 : BitVec 4) = 0x045#12`).
      return some (smt| (concat $(← emitTerm a) $(← emitTerm b)))
    -- Conversions between bit-vectors and the integers. `toNat` is unsigned
    -- (`bv2nat`), `toInt` two's-complement signed (`sbv_to_int`); `ofInt` wraps.
    -- Both operators are supported by z3 and cvc5 (checked).
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
      -- Same-width bit-vector amount: pad if the widths differ.
      return some (.symbApp op #[sa, bvResize false bw w (← emitTerm b)])
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
      return guardedQuantifierBody isForall cond body

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
    let partition ← partitionDefaultAppArgs fn args
    let valueArgs := partition.values
    let appExpr := mkAppN fn args
    -- Attempt finite-signature reification without changing fallback
    -- behavior. Success ties `fn` to an exact reified constant reference and
    -- its canonical flattened semantic certificate.
    let certifiedConstant? ← try
      let .pack reifiedSignature ← Metatheory.Reification.reifyTermSignature appExpr
      pure (Metatheory.Reification.certifyConstantIn? reifiedSignature fn)
    catch _ => pure none
    if certifiedConstant?.isNone then
      TranslateM.markTrusted (.constant fn)
    -- Preserve aliases for `emitSort`: a user sort handler may intentionally target a
    -- `def`-defined type. Structural keys normalize type components separately.
    let resTy ← instantiateMVars (← inferType appExpr)
    -- Key declarations by the complete instantiated signature, not just dropped
    -- type arguments. A polymorphic projection such as `Bind.toBind` may have no
    -- ordinary type argument while still being instantiated at different
    -- function-valued carriers. Reusing its first declaration then emits calls
    -- with incompatible `Fn` sorts (`unknown constant ... (Fn ...)` in z3).
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
    -- Record the symbol → Lean-head correspondence for proof replay. Applications are
    -- rebuilt from the head plus replayed arguments, so the *head* is what must be
    -- remembered; for a nullary symbol the head is the whole term.
    TranslateM.recordSymbolExpr name fn
    if !(← declaredFun name) then
      let argSorts ← valueArgs.mapM (fun a => do emitSort (← inferType a))
      let resSort ← emitSort resTy
      TranslateM.emitCommand (.declFun name argSorts resSort)
      if let some certified := certifiedConstant? then
        let emission : Metatheory.Reification.CertifiedSymbolBinding := {
          symbol := name
          constant := certified }
        let _ ← TranslateM.recordVerifiedConstant (Dynamic.mk emission)
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
