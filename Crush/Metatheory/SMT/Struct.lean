import Crush.Metatheory.SMT.Semantics

/-!
# Structures for SMT theory signatures

A `Struct sig` exposes only the literals and application symbols contained in
`sig`, while sharing the logical Boolean values and the sort carriers named by
that signature. It is a restricted view of the existing relational SMT model,
not a second term evaluator.
-/

namespace Crush.Metatheory.SMT

open Crush.SMT
open Crush.SMT.Theory

/-- Interpretation of one SMT theory signature. Membership arguments prevent a
theory from applying an identifier or reading a literal outside its signature. -/
structure Struct (sig : Sig) where
  Value : Type
  inSort : ∀ sort, sig.containsSort sort = true → Value → Prop
  bool : Bool → Value
  literal : ∀ value, sig.containsLiteral value = true → Value
  apply : ∀ identifier, sig.containsIdent identifier = true →
    List Value → Value → Prop

namespace Struct

/-- One-carrier interpretation of the empty signature. -/
def unit : Struct Sig.empty where
  Value := Unit
  inSort := by
    intro sort present value
    simp at present
  bool := fun _ => ()
  literal := by
    intro value present
    simp [Sig.containsLiteral, Sig.empty] at present
  apply := by
    intro identifier present
    simp [Sig.empty] at present

/-- Values have the listed sorts in one restricted structure. -/
inductive ValuesTyped {sig : Sig} (model : Struct sig) :
    List SSort → List model.Value → Prop where
  | nil : ValuesTyped model [] []
  | cons {sort sorts value values}
      (present : sig.containsSort sort = true)
      (head : model.inSort sort present value)
      (tail : ValuesTyped model sorts values) :
      ValuesTyped model (sort :: sorts) (value :: values)

namespace ValuesTyped

/-- An empty sort list types only an empty value list. -/
theorem eq_nil {sig : Sig} {model : Struct sig} {values : List model.Value}
    (typed : ValuesTyped model [] values) : values = [] := by
  cases typed
  rfl

/-- Invert one nonempty typed value list. -/
theorem exists_cons {sig : Sig} {model : Struct sig} {sort : SSort}
    {sorts : List SSort} {values : List model.Value}
    (typed : ValuesTyped model (sort :: sorts) values) :
    ∃ value rest, values = value :: rest ∧
      model.inSort sort (by
        cases typed
        assumption) value ∧
      ValuesTyped model sorts rest := by
  cases typed
  exact ⟨_, _, rfl, by assumption, by assumption⟩

end ValuesTyped

/-- Ordinary many-sorted structure laws for the vocabulary in `sig`.
Application typing is read from the same signature function used by the
checker. -/
structure WF {sig : Sig} (model : Struct sig) : Prop where
  sortNonempty : ∀ sort (present : sig.containsSort sort = true),
    ∃ value, model.inSort sort present value
  boolTyped : ∀ (present : sig.containsSort boolSort = true) value,
    model.inSort boolSort present (model.bool value)
  literalSort : ∀ literal,
    sig.containsLiteral literal = true →
      sig.containsSort literal.sort = true
  literalTyped : ∀ literal (present : sig.containsLiteral literal = true),
    model.inSort literal.sort (literalSort literal present)
      (model.literal literal present)
  appTyped : ∀ identifier
      (present : sig.containsIdent identifier = true)
      (argumentSorts : List SSort) (resultSort : SSort),
    sig.inferApp? identifier (argumentSorts.map some).toArray =
      some (.ok (some resultSort)) →
    ∀ values, ValuesTyped model argumentSorts values →
      ∃ resultPresent : sig.containsSort resultSort = true,
      ∃ output : model.Value,
        model.inSort resultSort resultPresent output ∧
        model.apply identifier present values output ∧
        ∀ other, model.apply identifier present values other → other = output

/-- Restrict a structure along a signature inclusion. -/
def reduct {small large : Sig} (sub : small.Sub large)
    (model : Struct large) : Struct small where
  Value := model.Value
  inSort := fun sort present =>
    model.inSort sort (Sig.containsSort_mono sub sort present)
  bool := model.bool
  literal := fun value present =>
    model.literal value (by
      unfold Sig.containsLiteral at present ⊢
      cases found : small.literalSort? value with
      | none => simp [found] at present
      | some sort =>
        have larger := sub.literal value sort found
        simp [larger])
  apply := fun identifier present => model.apply identifier
    (sub.ident identifier present)

/-- Isomorphism of two structures over one signature. The carrier maps
preserve every observation available through that signature. -/
structure Iso {sig : Sig} (left right : Struct sig) where
  to : left.Value → right.Value
  inv : right.Value → left.Value
  to_inv : ∀ value, to (inv value) = value
  inv_to : ∀ value, inv (to value) = value
  inSort : ∀ sort (present : sig.containsSort sort = true) value,
    left.inSort sort present value ↔ right.inSort sort present (to value)
  bool : ∀ value, to (left.bool value) = right.bool value
  literal : ∀ value (present : sig.containsLiteral value = true),
    to (left.literal value present) = right.literal value present
  apply : ∀ identifier (present : sig.containsIdent identifier = true)
      values output,
    left.apply identifier present values output ↔
      right.apply identifier present (values.map to) (to output)

namespace Iso

/-- Identity structure isomorphism. -/
def refl {sig : Sig} (model : Struct sig) : Iso model model where
  to := id
  inv := id
  to_inv := by simp
  inv_to := by simp
  inSort := by simp
  bool := by simp
  literal := by simp
  apply := by simp

/-- Mapping backward and then forward is the identity on value lists. -/
theorem map_map_to_inv {sig : Sig} {left right : Struct sig}
    (iso : Iso left right)
    (values : List right.Value) :
    (values.map iso.inv).map iso.to = values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [iso.to_inv, ih]

/-- Reverse a structure isomorphism. -/
def symm {sig : Sig} {left right : Struct sig}
    (iso : Iso left right) : Iso right left where
  to := iso.inv
  inv := iso.to
  to_inv := iso.inv_to
  inv_to := iso.to_inv
  inSort := by
    intro sort present value
    have preserved := iso.inSort sort present (iso.inv value)
    simpa [iso.to_inv] using preserved.symm
  bool := by
    intro value
    have equal := congrArg iso.inv (iso.bool value)
    simpa [iso.inv_to] using equal.symm
  literal := by
    intro value present
    have equal := congrArg iso.inv (iso.literal value present)
    simpa [iso.inv_to] using equal.symm
  apply := by
    intro identifier present values output
    have preserved := iso.apply identifier present
      (values.map iso.inv) (iso.inv output)
    rw [map_map_to_inv iso values] at preserved
    simpa [iso.to_inv] using preserved.symm

/-- Map a well-sorted value list through a structure isomorphism. -/
theorem valuesTyped_to {sig : Sig} {left right : Struct sig}
    (iso : Iso left right) :
    ∀ {sorts values}, ValuesTyped left sorts values →
      ValuesTyped right sorts (values.map iso.to)
  | _, _, .nil => .nil
  | _, _, .cons present head tail =>
      .cons present ((iso.inSort _ present _).mp head)
        (valuesTyped_to iso tail)

/-- Restrict an isomorphism to a smaller signature. -/
def reduct {small large : Sig} (sub : small.Sub large)
    {left right : Struct large} (iso : Iso left right) :
    Iso (Struct.reduct sub left) (Struct.reduct sub right) where
  to := iso.to
  inv := iso.inv
  to_inv := iso.to_inv
  inv_to := iso.inv_to
  inSort := by
    intro sort present value
    exact iso.inSort sort (Sig.containsSort_mono sub sort present) value
  bool := iso.bool
  literal := by
    intro value present
    apply iso.literal
  apply := by
    intro identifier present values output
    exact iso.apply identifier (sub.ident identifier present) values output

end Iso

namespace WF

/-- The empty signature has a concrete well-formed structure. -/
theorem unit : WF Struct.unit where
  sortNonempty := by
    intro sort present
    simp at present
  boolTyped := by simp
  literalSort := by
    intro literal present
    simp [Sig.containsLiteral, Sig.empty] at present
  literalTyped := by
    intro literal present
    simp [Sig.containsLiteral, Sig.empty] at present
  appTyped := by
    intro identifier present
    simp [Sig.empty] at present

/-- Every list of sorts formed by a well-formed signature has a pointwise
typed value list. This lemma makes the premise of `appTyped` visibly
inhabited. -/
theorem valuesTyped_exists {sig : Sig} {model : Struct sig}
    (wf : model.WF) : ∀ sorts,
    sig.containsSortList sorts = true →
      ∃ values, ValuesTyped model sorts values
  | [], present => ⟨[], .nil⟩
  | sort :: sorts, present => by
      have parts : sig.containsSort sort = true ∧
          sig.containsSortList sorts = true := by
        simpa only [Sig.containsSortList_cons, Bool.and_eq_true] using present
      rcases wf.sortNonempty sort parts.1 with ⟨value, typed⟩
      rcases valuesTyped_exists wf sorts parts.2 with ⟨values, rest⟩
      exact ⟨value :: values, .cons parts.1 typed rest⟩

/-- Every complete operator typing in a well-formed signature has a typed
input and a unique typed output in every well-formed structure. Thus operator
totality cannot hold merely because its input sorts are missing. -/
theorem app_exists {sig : Sig} (sigWF : sig.WF) {model : Struct sig}
    (wf : model.WF) {identifier : Ident} {argumentSorts : List SSort}
    {resultSort : SSort}
    (inferred : sig.inferApp? identifier
      (argumentSorts.map some).toArray = some (.ok (some resultSort))) :
    ∃ values output,
      ValuesTyped model argumentSorts values ∧
      model.inSort resultSort (sigWF.appSorts identifier argumentSorts
        resultSort inferred).2 output ∧
      model.apply identifier
        (sig.inferApp_present identifier (argumentSorts.map some).toArray
          (by rw [inferred]; rfl)) values output := by
  have closed := sigWF.appSorts identifier argumentSorts resultSort inferred
  rcases valuesTyped_exists wf argumentSorts closed.1 with ⟨values, typed⟩
  let present := sig.inferApp_present identifier
    (argumentSorts.map some).toArray (by rw [inferred]; rfl)
  rcases wf.appTyped identifier present argumentSorts resultSort inferred
      values typed with
    ⟨resultPresent, output, outputTyped, applied, unique⟩
  refine ⟨values, output, typed, ?_, ?_⟩
  · simpa only using outputTyped
  · simpa only using applied

/-- Well-formedness is invariant under structure isomorphism. -/
theorem ofIso {sig : Sig} {left right : Struct sig} (iso : Iso left right)
    (wf : WF left) : WF right where
  sortNonempty := by
    intro sort present
    rcases wf.sortNonempty sort present with ⟨value, typed⟩
    exact ⟨iso.to value, (iso.inSort sort present value).mp typed⟩
  boolTyped := by
    intro present value
    have typed := wf.boolTyped present value
    have mapped := (iso.inSort boolSort present _).mp typed
    simpa only [iso.bool] using mapped
  literalSort := wf.literalSort
  literalTyped := by
    intro literal present
    have typed := wf.literalTyped literal present
    have mapped :=
      (iso.inSort literal.sort (wf.literalSort literal present) _).mp typed
    simpa only [iso.literal] using mapped
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    have inverseTyped := Iso.valuesTyped_to iso.symm typed
    rcases wf.appTyped identifier present argumentSorts resultSort inferred
        (values.map iso.inv) inverseTyped with
      ⟨resultPresent, output, outputTyped, applied, unique⟩
    refine ⟨resultPresent, iso.to output,
      (iso.inSort resultSort resultPresent output).mp outputTyped, ?_, ?_⟩
    · have preserved := (iso.apply identifier present
          (values.map iso.inv) output).mp applied
      rw [Iso.map_map_to_inv iso values] at preserved
      exact preserved
    · intro other otherApplied
      have inverseApplied :
          left.apply identifier present (values.map iso.inv) (iso.inv other) := by
        have preserved := iso.apply identifier present
          (values.map iso.inv) (iso.inv other)
        apply preserved.mpr
        rw [Iso.map_map_to_inv iso values]
        simpa [iso.to_inv] using otherApplied
      have inverseEqual := unique (iso.inv other) inverseApplied
      have mappedEqual := congrArg iso.to inverseEqual
      simpa [iso.to_inv] using mappedEqual

end WF

end Struct

/-- Restrict a full relational SMT model to one theory signature. Boolean
literals use the distinguished Boolean interpretation employed by `Eval`. -/
def Model.reduct (model : Model) (sig : Sig) : Struct sig where
  Value := model.Value
  inSort := fun sort _ => model.inSort sort
  bool := model.bool
  literal := fun literal _ =>
    match literal with
    | .bool value => model.bool value
    | other => model.literal other
  apply := fun identifier _ => model.apply identifier

/-- Restricting a full model directly or through a larger signature gives the
same observations, up to the identity carrier map. This is the bridge between
the full-model presentation and SMT-LIB reduct-based theory combination. -/
def Model.reductSubIso (model : Model) {small large : Sig}
    (sub : small.Sub large) :
    Struct.Iso (Model.reduct model small)
      (Struct.reduct sub (Model.reduct model large)) where
  to := id
  inv := id
  to_inv := by simp
  inv_to := by simp
  inSort := by intro sort present value; rfl
  bool := by intro value; rfl
  literal := by
    intro literal present
    cases literal <;> rfl
  apply := by
    intro identifier present values output
    change model.apply identifier values output ↔
      model.apply identifier (values.map id) (id output)
    simp only [List.map_id_fun, id_eq]

/-- Re-index a typed value list between two restricted views of the same full
model once the destination signature contains all listed sorts. -/
theorem Struct.ValuesTyped.forSig (model : Model) {source target : Sig}
    {sorts : List SSort} {values : List model.Value}
    (closed : target.containsSortList sorts = true)
    (typed : Struct.ValuesTyped (Model.reduct model source) sorts values) :
    Struct.ValuesTyped (Model.reduct model target) sorts values := by
  induction sorts generalizing values with
  | nil =>
      have empty := Struct.ValuesTyped.eq_nil typed
      subst values
      exact .nil
  | cons sort sorts ih =>
      have parts : target.containsSort sort = true ∧
          target.containsSortList sorts = true := by
        simpa only [Sig.containsSortList_cons, Bool.and_eq_true] using closed
      rcases Struct.ValuesTyped.exists_cons typed with
        ⟨value, rest, rfl, head, tail⟩
      apply Struct.ValuesTyped.cons parts.1
      · change model.inSort sort value at head ⊢
        exact head
      · exact ih parts.2 tail

/-- Component well-formedness over one full model combines into
well-formedness of the least common signature. -/
theorem Model.reduct_sum_wf (model : Model) {left right : Sig}
    (leftSigWF : left.WF) (rightSigWF : right.WF)
    (compatible : left.Compatible right)
    (leftWF : (Model.reduct model left).WF)
    (rightWF : (Model.reduct model right).WF) :
    (Model.reduct model (left.sum right compatible)).WF where
  sortNonempty := by
    intro sort present
    exact model.sortNonempty sort
  boolTyped := by
    intro present value
    exact model.boolTyped value
  literalSort := (leftSigWF.sum rightSigWF compatible).literalSort
  literalTyped := by
    intro literal present
    cases literal with
    | bool value => exact model.boolTyped value
    | num value => exact model.literalTyped (.num value)
    | str value => exact model.literalTyped (.str value)
    | bitvec width value => exact model.literalTyped (.bitvec width value)
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    change (match left.inferApp? identifier
        (argumentSorts.map some).toArray with
      | some result => some result
      | none => right.inferApp? identifier
          (argumentSorts.map some).toArray) =
        some (.ok (some resultSort)) at inferred
    split at inferred
    next leftResult leftPresent =>
      have resultEq : leftResult = .ok (some resultSort) :=
        Option.some.inj inferred
      subst leftResult
      have closed := leftSigWF.appSorts identifier argumentSorts
        resultSort leftPresent
      have leftTyped := Struct.ValuesTyped.forSig model closed.1 typed
      let leftIdent := left.inferApp_present identifier
        (argumentSorts.map some).toArray (by rw [leftPresent]; rfl)
      rcases leftWF.appTyped identifier leftIdent argumentSorts resultSort
          leftPresent values leftTyped with
        ⟨leftResultPresent, output, outputTyped, applied, unique⟩
      refine ⟨((leftSigWF.sum rightSigWF compatible).appSorts identifier
        argumentSorts resultSort (by
          change (left.sum right compatible).inferApp? identifier
            (argumentSorts.map some).toArray = _
          simp [Sig.sum, leftPresent])).2, output, ?_, ?_, ?_⟩
      · change model.inSort resultSort output at outputTyped ⊢
        exact outputTyped
      · change model.apply identifier values output at applied ⊢
        exact applied
      · intro other otherApplied
        change model.apply identifier values other at otherApplied
        exact unique other otherApplied
    next leftAbsent =>
      have closed := rightSigWF.appSorts identifier argumentSorts
        resultSort inferred
      have rightTyped := Struct.ValuesTyped.forSig model closed.1 typed
      let rightIdent := right.inferApp_present identifier
        (argumentSorts.map some).toArray (by rw [inferred]; rfl)
      rcases rightWF.appTyped identifier rightIdent argumentSorts resultSort
          inferred values rightTyped with
        ⟨rightResultPresent, output, outputTyped, applied, unique⟩
      refine ⟨((leftSigWF.sum rightSigWF compatible).appSorts identifier
        argumentSorts resultSort (by
          change (left.sum right compatible).inferApp? identifier
            (argumentSorts.map some).toArray = _
          simp [Sig.sum, leftAbsent, inferred])).2, output, ?_, ?_, ?_⟩
      · change model.inSort resultSort output at outputTyped ⊢
        exact outputTyped
      · change model.apply identifier values output at applied ⊢
        exact applied
      · intro other otherApplied
        change model.apply identifier values other at otherApplied
        exact unique other otherApplied

end Crush.Metatheory.SMT
