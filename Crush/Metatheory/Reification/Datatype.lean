import Lean
import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.Reification.Term

/-!
# Certified reification of monomorphic Lean inductive blocks

Successful reification records the exact mutual declaration order, ground type
arguments, constructor order, and field order in a typed `Datatype.Block`.
Unsupported dependent, proof-valued, higher-order, or nonproductive declarations
return `none` at the existing partial Lean boundary.
-/

namespace Crush.Metatheory.Reification

open Lean Meta
open Crush.Metatheory.Datatype

/-- Structural reification before checking that every datatype in the block has
a finite value. -/
structure DatatypeShape where
  arity : Nat
  names : Array Name
  names_size : names.size = arity
  typeArgs : Array Expr
  externalTypes : Array Expr
  block : Block arity
  wf : block.WF

/-- One successfully reified, productive monomorphic mutual inductive block. -/
structure DatatypeBlock extends DatatypeShape where
  productive : Productive block

namespace DatatypeShape

/-- The typed datatype selected by one Lean mutual-block head. -/
def find? (reified : DatatypeShape) (name : Name) : Option (DataRef reified.block) :=
  match reified.names.findFinIdx? (· == name) with
  | none => none
  | some data => some ⟨data.val, by rw [← reified.names_size]; exact data.isLt⟩

end DatatypeShape

namespace DatatypeBlock

/-- The typed datatype selected by one Lean mutual-block head. -/
def find? (reified : DatatypeBlock) (name : Name) : Option (DataRef reified.block) :=
  reified.toDatatypeShape.find? name

end DatatypeBlock

/-- Why a user datatype could not enter the certified environment. -/
inductive DatatypeReject where
  /-- The named declaration is not an inductive datatype in the fragment
  understood by certified datatype reification. -/
  | unsupported (head : Name)
  /-- The datatype has indices, whose dependency would require an erasure or
  refinement proof not provided by the current monomorphic algebraic model. -/
  | indexed (head : Name)
  /-- The datatype declares no constructors, so its empty Lean carrier cannot
  be represented by a necessarily nonempty SMT sort. -/
  | empty (head : Name)
  /-- The inductive lives in `Prop`; proofs are not represented as free
  first-order datatype values. -/
  | prop (head : Name)
  /-- Required datatype parameters were omitted or were not fully instantiated,
  so there is no ground monomorphic datatype instance to declare. -/
  | parameters (head : Name)
  /-- The declaration is a typeclass. Treating instance synthesis data as a
  native free datatype would not preserve its intended elaboration semantics. -/
  | typeclass (head : Name)
  /-- This constructor field depends on an earlier field. The current field
  telescope supports only nondependent first-order field sorts. -/
  | dependentField (ctor : Name) (index : Nat)
  /-- This constructor field is proof-valued. Proof fields are outside the
  data-carrying first-order datatype semantics. -/
  | proofField (ctor : Name) (index : Nat)
  /-- This constructor field contains a function. Native datatype fields in the
  certified fragment must be first order. -/
  | functionField (ctor : Name) (index : Nat)
  /-- The term invokes a datatype recursor or auxiliary eliminator. Correctness
  of recursive elimination requires a separate theorem beyond declaration
  soundness. -/
  | recursor (name : Name)
  /-- The term uses a quotient primitive. Quotient equality is not the free
  constructor equality modeled by native SMT datatypes. -/
  | quotient (name : Name)
  /-- The recursive block has no finite constructor tree for at least one sort,
  so it cannot supply the nonempty well-founded carrier required by SMT. -/
  | nonproductive (head : Name)
  /-- Dependency discovery found recursion through a separately declared block.
  Such a cycle cannot be emitted as the single mutual block required by SMT. -/
  | cyclic (sort : String)
  /-- Dependency discovery exhausted its structural recursion bound, typically
  because nested monomorphic instantiations keep growing without reaching a
  finite declaration environment. -/
  | depth (type : Expr)
  deriving Inhabited, Repr

/-- Dependency-ordered monomorphic datatype blocks. -/
structure DatatypeEnv where
  blocks : Array DatatypeBlock

namespace DatatypeEnv

/-- All certified datatype sort identities in declaration order. -/
def sorts (env : DatatypeEnv) : List BaseSort :=
  env.blocks.toList.flatMap fun block => block.block.sorts

/-- Whether this environment contains a monomorphic instance of the given Lean
inductive head. -/
def containsHead (env : DatatypeEnv) (head : Name) : Bool :=
  env.blocks.any fun block => block.names.contains head

def signature (env : DatatypeEnv) : Signature :=
  env.blocks.toList.flatMap fun entry : DatatypeBlock => entry.block.symbolTypes

private def modelEntries : (blocks : List DatatypeBlock) →
    Datatype.Env (blocks.flatMap fun entry : DatatypeBlock => entry.block.symbolTypes)
  | [] => []
  | block :: blocks =>
      { arity := block.arity
        block := block.block
        symbols := block.block.symbols.inLeft
          (blocks.flatMap fun entry : DatatypeBlock => entry.block.symbolTypes) } ::
      (modelEntries blocks).inRight block.block.symbolTypes

private theorem modelEntries_length (blocks : List DatatypeBlock) :
    (modelEntries blocks).length = blocks.length := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      change Nat.succ ((modelEntries blocks).inRight
        block.block.symbolTypes).length = Nat.succ blocks.length
      rw [Datatype.Env.inRight_length, ih]

/-- Canonical datatype symbol environment over `signature`; datatype terms
remain ordinary source constants in this compact signature. -/
def toModelEnv (env : DatatypeEnv) : Datatype.Env env.signature :=
  modelEntries env.blocks.toList

@[simp] theorem toModelEnv_length (env : DatatypeEnv) :
    env.toModelEnv.length = env.blocks.size := by
  change (modelEntries env.blocks.toList).length = env.blocks.size
  rw [modelEntries_length]
  simp

/-- A typed position of one reified mutual block in its dependency-ordered
environment, together with the datatype selected inside that block. -/
structure FoundBlock (blocks : List DatatypeBlock) where
  block : DatatypeBlock
  ref : Datatype.Ref blocks block
  data : DataRef block.block

namespace FoundBlock

/-- The exact constructor selected inside a found datatype declaration. -/
structure Ctor {blocks : List DatatypeBlock} (found : FoundBlock blocks) where
  decl : CtorDecl found.block.arity
  ref : CtorRef found.block.block found.data decl

/-- Select a constructor by Lean's declaration index and confirm its full name. -/
def ctor? {blocks : List DatatypeBlock} (found : FoundBlock blocks) (name : Name)
    (index : Nat) : Option (Ctor found) := do
  let selected ← Datatype.Ref.at? found.data.decl.ctors index
  if selected.value.name == name.toString then
    return ⟨selected.value, selected.ref⟩
  none

namespace Ctor

/-- The exact field selected inside a found constructor. -/
structure Field {blocks : List DatatypeBlock} {found : FoundBlock blocks}
    (ctor : Ctor found) where
  decl : FieldDecl found.block.arity
  ref : FieldRef ctor.decl decl

/-- Select a field by Lean's projection metadata index. -/
def field? {blocks : List DatatypeBlock} {found : FoundBlock blocks}
    (ctor : Ctor found) (index : Nat) : Option (Field ctor) := do
  let selected ← Datatype.Ref.at? ctor.decl.fields index
  return ⟨selected.value, selected.ref⟩

end Ctor

/-- Lift a block-local source constant into the complete canonical datatype
signature without changing its type. -/
def lift {blocks : List DatatypeBlock} {block : DatatypeBlock}
    (ref : Datatype.Ref blocks block)
    {type : Ty} (constant : Const block.block.symbolTypes type) :
    Const (blocks.flatMap fun entry : DatatypeBlock => entry.block.symbolTypes) type := by
  apply Datatype.Ref.toConst
  exact ref.flatMap (fun entry => entry.block.symbolTypes)
    (Datatype.Ref.ofConst constant)

/-- Canonical symbol map for the selected block in the complete datatype
signature. -/
def symbols {blocks : List DatatypeBlock} (found : FoundBlock blocks) :
    Symbols (blocks.flatMap fun entry : DatatypeBlock => entry.block.symbolTypes)
      found.block.block :=
  match found with
  | ⟨block, ref, _⟩ => {
      ctor := fun ctor => lift ref (block.block.ctorConst ctor)
      sel := fun {_data} {_ctor} ctor {_field} field =>
        lift ref (block.block.selConst ctor field)
      test := fun ctor => lift ref (block.block.testConst ctor) }

end FoundBlock

end DatatypeEnv

/-- A certified datatype environment occupying a typed prefix of one complete
source signature. Ordinary constants remain in `tail`. -/
structure DatatypeSignaturePrefix (signature : Signature) where
  env : DatatypeEnv
  tail : Signature
  signature_eq : signature = env.signature ++ tail

namespace DatatypeSignaturePrefix

/-- Canonical reified for a datatype prefix followed by an ordinary signature. -/
def of (env : DatatypeEnv) (tail : Signature) :
    DatatypeSignaturePrefix (env.signature ++ tail) :=
  { env, tail, signature_eq := rfl }

/-- The datatype symbol environment weakened across the ordinary signature tail. -/
def toModelEnv {signature : Signature} (reified : DatatypeSignaturePrefix signature) :
    Datatype.Env signature :=
  reified.signature_eq.symm ▸ reified.env.toModelEnv.inLeft reified.tail

@[simp] theorem of_toModelEnv_length (env : DatatypeEnv) (tail : Signature) :
    (DatatypeSignaturePrefix.of env tail).toModelEnv.length = env.blocks.size := by
  simp [toModelEnv, of, Datatype.Env.inLeft]

/-- Lift the exact symbol map of a found block through the complete source
signature represented by this datatype prefix. -/
def symbols {signature : Signature} (reified : DatatypeSignaturePrefix signature)
    (found : DatatypeEnv.FoundBlock reified.env.blocks.toList) :
    Symbols signature found.block.block := by
  exact Eq.mpr
    (congrArg (fun types => Symbols types found.block.block) reified.signature_eq)
    (found.symbols.inLeft reified.tail)

end DatatypeSignaturePrefix

private def renderedSort (head : Name) (typeArgs : Array Expr) : MetaM BaseSort := do
  let constant ← mkConstWithFreshMVarLevels head
  return ⟨toString (← ppExpr (mkAppN constant typeArgs))⟩

private def sameArgs (left right : Array Expr) : MetaM Bool := do
  if left.size != right.size then return false
  for index in [:left.size] do
    unless ← isDefEqGuarded left[index]! right[index]! do return false
  return true

namespace DatatypeEnv

private partial def findIn? : (blocks : List DatatypeBlock) → (head : Name) →
    (typeArgs : Array Expr) → MetaM (Option (FoundBlock blocks))
  | [], _, _ => return none
  | block :: rest, head, typeArgs => do
      if ← sameArgs block.typeArgs typeArgs then
        if let some data := block.find? head then
          return some { block, ref := .here, data }
      let some found ← findIn? rest head typeArgs | return none
      return some { block := found.block, ref := .there found.ref, data := found.data }

/-- Find the exact monomorphic datatype declaration in the dependency-ordered
environment. Both the declaration head and all type arguments must agree. -/
partial def find? (env : DatatypeEnv) (head : Name) (typeArgs : Array Expr) :
    MetaM (Option (FoundBlock env.blocks.toList)) :=
  findIn? env.blocks.toList head typeArgs

/-- Exact metadata result for one fully applied constructor occurrence. -/
structure CtorApp (env : DatatypeEnv) where
  head : Expr
  name : Name
  induct : Name
  found : FoundBlock env.blocks.toList
  ctor : found.Ctor
  typeArgs : Array Expr
  values : Array Expr

/-- Recognize a complete constructor occurrence once for both term construction
and structural-witness erasure. -/
partial def ctorApp? (env : DatatypeEnv) (expression : Expr) :
    MetaM (Option (CtorApp env)) := do
  let head := expression.getAppFn
  let .const name _ := head | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  let arguments := expression.getAppArgs
  if arguments.size < info.numParams then return none
  let typeArgs := arguments.extract 0 info.numParams
  let some found ← env.find? info.induct typeArgs | return none
  let some ctor := found.ctor? name info.cidx | return none
  if arguments.size != info.numParams + ctor.decl.fields.length then return none
  return some {
    head
    name
    induct := info.induct
    found
    ctor
    typeArgs
    values := arguments.extract info.numParams arguments.size }

/-- Exact metadata result for one supported projection occurrence. -/
structure ProjApp (env : DatatypeEnv) where
  head : Expr
  name : Name
  ctorName : Name
  fieldIndex : Nat
  found : FoundBlock env.blocks.toList
  ctor : found.Ctor
  field : ctor.Field
  typeArgs : Array Expr
  target : Expr

/-- Recognize a non-function-valued projection once for both term construction
and structural-witness erasure. -/
partial def projApp? (env : DatatypeEnv) (expression : Expr) :
    MetaM (Option (ProjApp env)) := do
  let head := expression.getAppFn
  let .const name _ := head | return none
  let some info ← getProjectionFnInfo? name | return none
  let arguments := expression.getAppArgs
  if arguments.size != info.numParams + 1 then return none
  let typeArgs := arguments.extract 0 info.numParams
  let some target := arguments[info.numParams]? | return none
  let ctorInfo ← getConstInfoCtor info.ctorName
  let some found ← env.find? ctorInfo.induct typeArgs | return none
  let some ctor := found.ctor? info.ctorName ctorInfo.cidx | return none
  let some field := ctor.field? info.i | return none
  return some {
    head
    name
    ctorName := info.ctorName
    fieldIndex := info.i
    found
    ctor
    field
    typeArgs
    target }

end DatatypeEnv

private def isBuiltin (name : Name) : Bool :=
  name == ``Nat || name == ``Int || name == ``Bool || name == ``String ||
    name == ``Array || name == ``BitVec

/-- Most specific structural reason available when block reification fails. -/
private partial def rejectReason (head : Name) (typeArgs : Array Expr) :
    MetaM DatatypeReject := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? head | return .unsupported head
  if info.numIndices != 0 then return .indexed head
  if info.ctors.isEmpty then return .empty head
  if info.numParams != typeArgs.size then return .parameters head
  if isClass env head then return .typeclass head
  unless (match info.type.getForallBody with
      | .sort level => !level.isZero
      | _ => false) do
    return .prop head
  for argument in typeArgs do
    let argument ← instantiateMVars argument
    if argument.hasExprMVar || argument.hasFVar then return .parameters head
    unless (← whnf (← inferType argument)).isSort do return .parameters head
  for ctorName in info.ctors do
    let ctor ← getConstInfoCtor ctorName
    let ctorType ← instantiateForall ctor.type typeArgs
    let reason? ← forallTelescopeReducing ctorType fun fields _ => do
      for index in [:fields.size] do
        let type ← whnf (← inferType fields[index]!)
        if type.hasFVar then return some (.dependentField ctorName index)
        if type.isForall then return some (.functionField ctorName index)
        if ← isProp type then return some (.proofField ctorName index)
      return none
    if let some reason := reason? then return reason
  return .unsupported head

/-- Reify one constructor field. A direct reference to the current mutual block
becomes a typed recursive reference; every other accepted field remains an
external base carrier. -/
private partial def reifyField? (names : Array Name)
    (typeArgs : Array Expr) (index : Nat) (field : Expr) :
    MetaM (Option (FieldDecl names.size × Option Expr)) := do
  let type ← whnf (← inferType field)
  if type.isForall || type.hasFVar || (← isProp type) then return none
  let userName ← field.fvarId!.getUserName
  let fieldName :=
    if userName.isAnonymous then s!"field_{index}" else userName.toString
  match type.getAppFn with
  | .const head _ =>
      if let some data := names.findFinIdx? (· == head) then
        if ← sameArgs type.getAppArgs typeArgs then
          return some ({ name := fieldName, sort := .data data }, none)
  | _ => pure ()
  let reified ← reifyType type
  match reified with
  | .base _ sort =>
      return some ({ name := fieldName, sort := .base sort }, some type)
  | .bool _ | .arrow .. => return none

private partial def reifyCtor? (names : Array Name)
    (typeArgs : Array Expr) (ctorName : Name) :
    MetaM (Option (CtorDecl names.size × Array Expr)) := do
  let info ← getConstInfoCtor ctorName
  let type ← instantiateForall info.type typeArgs
  forallTelescopeReducing type fun fields _ => do
    let mut result : Array (FieldDecl names.size) := #[]
    let mut externalTypes : Array Expr := #[]
    for index in [:fields.size] do
      let some (field, external?) ← reifyField? names typeArgs index fields[index]!
        | return none
      result := result.push field
      if let some type := external? then
        unless externalTypes.contains type do externalTypes := externalTypes.push type
    return some ({ name := ctorName.toString, fields := result.toList }, externalTypes)

private partial def reifyDecl? (names : Array Name)
    (typeArgs : Array Expr) (name : Name) :
    MetaM (Option (DataDecl names.size × Array Expr)) := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? name | return none
  if info.numIndices != 0 || info.numParams != typeArgs.size || info.ctors.isEmpty then
    return none
  let mut ctors : Array (CtorDecl names.size) := #[]
  let mut externalTypes : Array Expr := #[]
  for ctorName in info.ctors do
    let some (ctor, ctorExternal) ← reifyCtor? names typeArgs ctorName | return none
    ctors := ctors.push ctor
    for type in ctorExternal do
      unless externalTypes.contains type do externalTypes := externalTypes.push type
  return some ({ sort := ← renderedSort name typeArgs, ctors := ctors.toList }, externalTypes)

/-- Reify the structural first datatype fragment before checking productivity. -/
partial def reifyDatatypeShape? (name : Name) (typeArgs : Array Expr) :
    MetaM (Option DatatypeShape) := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? name | return none
  if info.numIndices != 0 || info.numParams != typeArgs.size || info.ctors.isEmpty then
    return none
  if isClass env name then return none
  if isBuiltin name then return none
  unless (match info.type.getForallBody with
      | .sort level => !level.isZero
      | _ => false) do
    return none
  for argument in typeArgs do
    let argument ← instantiateMVars argument
    if argument.hasExprMVar || argument.hasFVar then return none
    unless (← whnf (← inferType argument)).isSort do return none
  let names := info.all.toArray
  let arity := names.size
  if arity == 0 then return none
  let mut decls : Array (DataDecl arity) := #[]
  let mut externalTypes : Array Expr := #[]
  for mutualName in names do
    let some (decl, declExternal) ← reifyDecl? names typeArgs mutualName | return none
    decls := decls.push decl
    for type in declExternal do
      unless externalTypes.contains type do externalTypes := externalTypes.push type
  if size_eq : decls.size = arity then
    let block := Block.ofArray decls size_eq
    if wfCheck : block.wellFormed = true then
      return some {
        arity
        names
        names_size := rfl
        typeArgs
        externalTypes
        block
        wf := (Block.wellFormed_eq_true block).mp wfCheck }
  return none

/-- Reify the first certified datatype fragment from one fully applied inductive
head. This function is partial only because Lean metadata normalization and
telescope traversal are partial metaprogramming operations; the returned
reified block and its semantic translation are total. -/
partial def reifyDatatypeBlock? (name : Name) (typeArgs : Array Expr) :
    MetaM (Option DatatypeBlock) := do
  let some shape ← reifyDatatypeShape? name typeArgs | return none
  if productiveCheck : shape.block.productive = true then
    return some {
      toDatatypeShape := shape
      productive := Block.productive_sound shape.block productiveCheck }
  return none

private partial def visitDatatype (fuel : Nat) (visiting : Array String)
    (blocks : Array DatatypeBlock) (type : Expr) :
    MetaM (Except DatatypeReject (Array DatatypeBlock)) := do
  match fuel with
  | 0 => return .error (.depth type)
  | fuel + 1 =>
    let type ← whnf type
    let .const head _ := type.getAppFn | return .ok blocks
    if isBuiltin head then return .ok blocks
    let env ← getEnv
    let some (.inductInfo _) := env.find? head | return .ok blocks
    let some shape ← reifyDatatypeShape? head type.getAppArgs
      | return .error (← rejectReason head type.getAppArgs)
    let keys := shape.block.sorts.map (·.name)
    if blocks.any fun existing =>
        existing.block.sorts.any fun sort => keys.contains sort.name then
      return .ok blocks
    if let some key := keys.find? visiting.contains then
      return .error (.cyclic key)
    let mut result := blocks
    let active := visiting ++ keys.toArray
    for external in shape.externalTypes do
      match ← visitDatatype fuel active result external with
      | .error reason => return .error reason
      | .ok updated => result := updated
    if productiveCheck : shape.block.productive = true then
      let certified : DatatypeBlock := {
        toDatatypeShape := shape
        productive := Block.productive_sound shape.block productiveCheck }
      return .ok (result.push certified)
    return .error (.nonproductive head)

/-- Collect datatype blocks reachable from the given ground types in dependency
order. The fuel bounds strictly growing nested instantiations such as
`Bush (Bush α)` that cannot be represented by a finite family of monomorphic SMT
declarations. -/
partial def reifyDatatypeEnv (roots : Array Expr) (fuel := 64) :
    MetaM (Except DatatypeReject DatatypeEnv) := do
  let mut blocks : Array DatatypeBlock := #[]
  for root in roots do
    match ← visitDatatype fuel #[] blocks root with
    | .error reason => return .error reason
    | .ok updated => blocks := updated
  return .ok { blocks }

/-- A supported ground datatype application together with every earlier native
dependency discovered for it. `block` is the mutual block containing `head`, and
`data` is the exact declaration selected by that head. This is the shared
acceptance result consumed by both certified reification and the Crush translator. -/
structure DatatypeApp where
  head : Name
  typeArgs : Array Expr
  env : DatatypeEnv
  block : DatatypeBlock
  data : DataRef block.block

/-- Certify one fully applied monomorphic datatype head. Dependency discovery is
part of acceptance, so cross-block indirect recursion is rejected here rather
than by a second translator-only predicate. -/
partial def reifyDatatypeApp (head : Name) (typeArgs : Array Expr)
    (fuel := 64) : MetaM (Except DatatypeReject DatatypeApp) := do
  let constant ← mkConstWithFreshMVarLevels head
  let root := mkAppN constant typeArgs
  match ← reifyDatatypeEnv #[root] fuel with
  | .error reason => return .error reason
  | .ok env =>
      let some block := env.blocks.back?
        | return .error (.unsupported head)
      let some data := block.find? head
        | return .error (.unsupported head)
      return .ok { head, typeArgs, env, block, data }

end Crush.Metatheory.Reification
