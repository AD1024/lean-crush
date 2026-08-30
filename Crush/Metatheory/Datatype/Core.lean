import Crush.Metatheory.HO.Core

/-!
# Intrinsic descriptions of monomorphic datatype blocks

This module describes the structural fragment shared by Lean inductive blocks
and SMT-LIB `declare-datatypes`.  It is independent of both `Lean.Expr` and the
raw SMT syntax.

A block has a statically known number of mutually recursive datatype sorts.
Constructor fields either use an external base carrier or refer directly to one
sort in the same block.  The latter restriction makes unsafe cross-block cycles
unrepresentable.
-/

namespace Crush.Metatheory.Datatype

universe u v

/-- A typed position in a list. Positions, rather than names, preserve Lean's
declaration order and distinguish equal-looking declarations. -/
inductive Ref {α : Type u} : (values : List α) → α → Type u where
  | here {value : α} {values : List α} : Ref (value :: values) value
  | there {value head : α} {values : List α} :
      Ref values value → Ref (head :: values) value
  deriving Repr

namespace Ref

/-- An element together with its typed position in a list. -/
structure Found {α : Type u} (values : List α) where
  value : α
  ref : Ref values value

/-- Every list entry paired with its intrinsic typed position, in source
order. -/
def all {α : Type u} : (values : List α) → List (Found values)
  | [] => []
  | value :: rest =>
      ⟨value, .here⟩ :: (all rest).map fun found =>
        ⟨found.value, .there found.ref⟩

@[simp] theorem all_length {α : Type u} (values : List α) :
    (all values).length = values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [all, ih]

@[simp] theorem mem_all {α : Type u} {values : List α} {value : α}
    (ref : Ref values value) :
    (⟨value, ref⟩ : Found values) ∈ all values := by
  induction ref with
  | here => simp [all]
  | there ref ih =>
      simp only [all, List.mem_cons, List.mem_map]
      right
      exact ⟨⟨_, ref⟩, ih, rfl⟩

/-- Quantifying over the finite enumeration is equivalent to quantifying over
typed references directly. -/
theorem all_iff {α : Type u} (values : List α)
    (property : ∀ value, Ref values value → Prop) :
    (∀ found ∈ all values, property found.value found.ref) ↔
      ∀ value (ref : Ref values value), property value ref := by
  constructor
  · intro every value ref
    exact every ⟨value, ref⟩ (mem_all ref)
  · intro every found member
    exact every found.value found.ref

/-- Map a typed position through a list map without changing its index. -/
def map {α : Type u} {β : Type v} {values : List α} {value : α}
    (ref : Ref values value) (image : α → β) :
    Ref (values.map image) (image value) :=
  match ref with
  | .here => .here
  | .there ref => .there (ref.map image)

/-- Embed a position in the left side of an append. -/
def inLeft {α : Type u} {values : List α} {value : α}
    (ref : Ref values value) (tail : List α) :
    Ref (values ++ tail) value :=
  match ref with
  | .here => .here
  | .there ref => .there (ref.inLeft tail)

/-- Embed a position in the right side of an append. -/
def inRight {α : Type u} (head : List α) {values : List α} {value : α}
    (ref : Ref values value) : Ref (head ++ values) value :=
  match head with
  | [] => ref
  | _ :: head => .there (ref.inRight head)

/-- Compose an outer and inner position through `List.flatMap`. -/
def flatMap {α : Type u} {β : Type v} {values : List α} {value : α}
    (outer : Ref values value) (image : α → List β)
    {result : β} (inner : Ref (image value) result) :
    Ref (values.flatMap image) result :=
  match outer with
  | @here _ _ tail => inner.inLeft (tail.flatMap image)
  | @there _ _ head tail outer =>
      (outer.flatMap image inner).inRight (image head)

/-- Zero-based position of a typed list reference. -/
def index {α : Type u} : {values : List α} → {value : α} →
    Ref values value → Nat
  | _ :: _, _, .here => 0
  | _ :: _, _, .there ref => index ref + 1

@[simp] theorem index_lt {α : Type u} {values : List α} {value : α}
    (ref : Ref values value) : ref.index < values.length := by
  induction ref with
  | here => simp [index]
  | there ref ih => simp [index, ih]

@[simp] theorem getElem_index {α : Type u} {values : List α} {value : α}
    (ref : Ref values value) : values[ref.index] = value := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih

@[simp] theorem getElem?_index {α : Type u} {values : List α} {value : α}
    (ref : Ref values value) : values[ref.index]? = some value := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih

/-- Recover the intrinsic reference at a known in-bounds position. -/
def ofIdx {α : Type u} : (values : List α) → (index : Nat) →
    (inBounds : index < values.length) → Ref values values[index]
  | _ :: _, 0, _ => .here
  | _ :: rest, index + 1, inBounds =>
      .there (ofIdx rest index (Nat.lt_of_succ_lt_succ inBounds))

/-- Recover a typed list position when the runtime index is in bounds. -/
def at? {α : Type u} (values : List α) (index : Nat) : Option (Found values) :=
  if inBounds : index < values.length then
    some ⟨values[index], ofIdx values index inBounds⟩
  else
    none

/-- Find the first value satisfying a Boolean predicate and retain its typed
position. -/
def find? {α : Type u} (values : List α) (accept : α → Bool) :
    Option (Found values) :=
  match values with
  | [] => none
  | value :: rest =>
      if accept value then
        some ⟨value, .here⟩
      else
        match find? rest accept with
        | none => none
        | some ⟨found, ref⟩ => some ⟨found, .there ref⟩

/-- The typed position of an element in a finite enumeration. -/
def ofFn {α : Type u} {size : Nat} (value : Fin size → α)
    (index : Fin size) : Ref (List.ofFn value) (value index) := by
  let ref := ofIdx (List.ofFn value) index.val (by simp)
  simpa using ref

@[simp] theorem index_ofIdx {α : Type u} (values : List α) (index : Nat)
    (inBounds : index < values.length) :
    (ofIdx values index inBounds).index = index := by
  induction values generalizing index with
  | nil => contradiction
  | cons value rest ih =>
      cases index with
      | zero => rfl
      | succ index => simp [ofIdx, Ref.index, ih]

/-- A position determines an intrinsic reference, including its selected value. -/
theorem heq_of_index_eq {α : Type u} {values : List α} {leftValue rightValue : α}
    (left : Ref values leftValue) (right : Ref values rightValue)
    (equal : left.index = right.index) : HEq left right := by
  have valueEq : leftValue = rightValue := by
    have selected := getElem?_index left
    rw [equal, getElem?_index right] at selected
    exact Option.some.inj selected.symm
  subst rightValue
  apply heq_of_eq
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there right => simp [index] at equal
  | there left ih =>
      cases right with
      | here => simp [index] at equal
      | there right =>
          congr 1
          exact ih right (Nat.add_right_cancel equal)

/-- A typed reference selects the matching entry of an indexed map. -/
theorem mem_mapIdx {α : Type u} {β : Type v} {values : List α} {value : α}
    (ref : Ref values value) (image : Nat → α → β) :
    image ref.index value ∈ values.mapIdx image := by
  induction ref generalizing image with
  | here => simp [index, List.mapIdx_cons]
  | there ref ih =>
      simp only [index, List.mapIdx_cons, List.mem_cons]
      right
      exact ih (fun index value => image (index + 1) value)

end Ref

/-- An injective map preserves duplicate-freedom. Kept here because datatype
encoders use the same fact for intrinsic positions and allocated names. -/
theorem nodup_map {α β : Type} {values : List α} {image : α → β}
    (nodup : values.Nodup) (injective : Function.Injective image) :
    (values.map image).Nodup := by
  induction nodup with
  | nil => exact .nil
  | @cons value values fresh _ ih =>
      apply List.Pairwise.cons
      · intro mapped member equal
        rw [List.mem_map] at member
        rcases member with ⟨other, otherMem, imageEq⟩
        exact fresh other otherMem (injective (equal.trans imageEq.symm))
      · exact ih

/-- The canonical finite enumeration contains each position once. -/
theorem finRange_nodup (arity : Nat) : (List.finRange arity).Nodup := by
  induction arity with
  | zero => simp
  | succ arity ih =>
      rw [List.finRange_succ]
      exact List.Pairwise.cons (by
        intro value member equal
        rw [List.mem_map] at member
        rcases member with ⟨source, sourceMem, rfl⟩
        exact Fin.succ_ne_zero source equal.symm)
        (nodup_map ih fun left right equal => Fin.succ_inj.mp equal)

/-- Sort of a constructor field. An external field is interpreted by a carrier
supplied to the block; a recursive field points into the current mutual block. -/
inductive FieldSort (arity : Nat) where
  | base : BaseSort → FieldSort arity
  | data : Fin arity → FieldSort arity
  deriving BEq, DecidableEq, Repr

/-- One named constructor field. Field names are descriptive metadata; typed
references use positions so duplicate Lean field names remain harmless here. -/
structure FieldDecl (arity : Nat) where
  name : String
  sort : FieldSort arity
  deriving BEq, DecidableEq, Repr

/-- One constructor in a mutual datatype block. -/
structure CtorDecl (arity : Nat) where
  name : String
  fields : List (FieldDecl arity)
  deriving BEq, DecidableEq, Repr

/-- One datatype sort and its constructors. -/
structure DataDecl (arity : Nat) where
  sort : BaseSort
  ctors : List (CtorDecl arity)
  deriving BEq, DecidableEq, Repr

/-- A mutually recursive datatype block with exactly `arity` datatype sorts. -/
structure Block (arity : Nat) where
  decl : Fin arity → DataDecl arity

namespace Block

/-- Executable structural equality for finite datatype blocks.  Comparing the
finite declaration list, rather than proof or Lean-metadata fields, is the
boundary needed when production reconnects an existentially stored native
command to its intrinsically indexed block. -/
def same {arity : Nat} (left right : Block arity) : Bool :=
  decide (List.ofFn left.decl = List.ofFn right.decl)

@[simp] theorem same_eq_true {arity : Nat} {left right : Block arity} :
    left.same right = true ↔ left = right := by
  constructor
  · intro equal
    cases left with
    | mk leftDecl =>
      cases right with
      | mk rightDecl =>
        congr
        funext index
        have lists : List.ofFn leftDecl = List.ofFn rightDecl := by
          exact of_decide_eq_true equal
        have selected := congrArg (fun values => values[index.val]?) lists
        simpa using selected
  · intro equal
    subst right
    exact decide_eq_true rfl

instance {arity : Nat} : BEq (Block arity) := ⟨same⟩

instance {arity : Nat} : LawfulBEq (Block arity) where
  rfl := by
    intro block
    change block.same block = true
    exact same_eq_true.mpr rfl
  eq_of_beq := by
    intro left right equal
    change left.same right = true at equal
    exact same_eq_true.mp equal

instance {arity : Nat} : DecidableEq (Block arity) := fun left right =>
  if equal : left.same right = true then
    isTrue (same_eq_true.mp equal)
  else
    isFalse fun assumed => equal (same_eq_true.mpr assumed)

end Block

/-- Existential package for the arity-indexed intrinsic content of a datatype
block. Lean declaration metadata is intentionally absent: native command
ownership depends only on this finite typed description. -/
structure SomeBlock where
  arity : Nat
  block : Block arity
  deriving DecidableEq

/-- Build a block from an array whose size is the block arity. This is the form
used by executable Lean declaration reification. -/
def Block.ofArray {arity : Nat} (decls : Array (DataDecl arity))
    (size_eq : decls.size = arity) : Block arity where
  decl data :=
    decls[data.val]'(by rw [size_eq]; exact data.isLt)

/-- Typed reference to one datatype in a block. -/
abbrev DataRef {arity : Nat} (_block : Block arity) := Fin arity

/-- The declaration selected by a datatype reference. -/
def DataRef.decl {arity : Nat} {block : Block arity}
    (data : DataRef block) : DataDecl arity :=
  block.decl data

/-- Typed reference to one constructor of one datatype. -/
abbrev CtorRef {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) :=
  Ref data.decl.ctors ctor

/-- Typed reference to one field of one constructor. -/
abbrev FieldRef {arity : Nat} (ctor : CtorDecl arity)
    (field : FieldDecl arity) :=
  Ref ctor.fields field

namespace Block

/-- Datatype sort names in declaration order. -/
def sorts {arity : Nat} (block : Block arity) : List BaseSort :=
  List.ofFn fun data => (block.decl data).sort

/-- Base sorts used by fields classified as external to this mutual block. -/
def externalSorts {arity : Nat} (block : Block arity) : List BaseSort :=
  (List.ofFn fun data : Fin arity => block.decl data).flatMap fun decl =>
    decl.ctors.flatMap fun ctor =>
      ctor.fields.filterMap fun field =>
        match field.sort with
        | .base sort => some sort
        | .data _ => none

/-- Structural conditions not already enforced by the indices.

Productivity is semantic and is defined beside the canonical values: a block
such as `Loop = mk Loop` has a structurally legal declaration but no finite
value. -/
structure WF {arity : Nat} (block : Block arity) : Prop where
  nonempty : 0 < arity
  sorts_nodup : block.sorts.Nodup
  external_fresh : ∀ sort ∈ block.externalSorts, sort ∉ block.sorts

/-- Distinct datatype references in a well-formed mutual block have distinct
source base-sort identities. -/
theorem WF.data_eq {arity : Nat} {block : Block arity} (wf : block.WF)
    {left right : DataRef block}
    (equal : left.decl.sort = right.decl.sort) : left = right := by
  have leftLt : left.val < block.sorts.length := by
    simp [Block.sorts]
  have rightLt : right.val < block.sorts.length := by
    simp [Block.sorts]
  have selected : block.sorts[left.val]'leftLt =
      block.sorts[right.val]'rightLt := by
    simpa [Block.sorts, DataRef.decl] using equal
  exact Fin.ext ((List.getElem_inj wf.sorts_nodup).mp selected)

/-- A field tagged as external cannot name a datatype in the same mutual block. -/
theorem WF.base_ne_data {arity : Nat} {block : Block arity} (wf : block.WF)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) {base : BaseSort}
    (fieldEq : field.sort = .base base) (child : DataRef block) :
    base ≠ child.decl.sort := by
  intro equal
  have ctorMem : ctor ∈ data.decl.ctors := by
    exact Ref.getElem_index ctorRef ▸ List.getElem_mem _
  have fieldMem : field ∈ ctor.fields := by
    exact Ref.getElem_index fieldRef ▸ List.getElem_mem _
  have externalMem : base ∈ block.externalSorts := by
    simp only [externalSorts, List.mem_flatMap, List.mem_filterMap]
    refine ⟨data.decl, ?_, ctor, ctorMem, field, fieldMem, ?_⟩
    · simp [DataRef.decl]
    · rw [fieldEq]
  have dataMem : child.decl.sort ∈ block.sorts := by
    simp [Block.sorts, DataRef.decl]
  exact wf.external_fresh base externalMem (equal ▸ dataMem)

/-- Executable structural well-formedness check. -/
def wellFormed {arity : Nat} (block : Block arity) : Bool :=
  decide (0 < arity) && decide block.sorts.Nodup &&
    block.externalSorts.all fun sort => !block.sorts.contains sort

@[simp] theorem wellFormed_eq_true {arity : Nat} (block : Block arity) :
    block.wellFormed = true ↔ block.WF := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]
  exact ⟨fun ⟨⟨nonempty, nodup⟩, external⟩ =>
      ⟨nonempty, nodup, external⟩,
    fun wf => ⟨⟨wf.nonempty, wf.sorts_nodup⟩, wf.external_fresh⟩⟩

end Block

end Crush.Metatheory.Datatype
