import Crush.Metatheory.SMT.TheoryEnv

/-!
# Integer theory modeled by the SMT metatheory

This module packages the modeled integer fragment: the standard integer
carrier, natural-number literals, and `>=`. Further arithmetic operators remain
in the syntax-only registry until their semantic modules are added.
-/

namespace Crush.Metatheory.SMT.Int

open Crush.SMT
open Crush.SMT.Theory

/-- Interpretation evidence for the modeled integer signature. -/
structure Interp (model : Struct intSig) where
  int : Int → model.Value
  intTyped : ∀ value,
    model.inSort intSort (by simp) (int value)
  intInjective : Function.Injective int
  intExhaustive : ∀ value,
    model.inSort intSort (by simp) value →
      ∃ integer, value = int integer
  numeral : ∀ value : Nat,
    model.literal (.num value) (by rfl) = int value
  ge : ∀ left right output,
    model.apply (.symb ">=") (by rfl) [int left, int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false)

/-- Models of the integer theory are well-formed structures carrying
the standard integer interpretation. -/
def Models (model : Struct intSig) : Prop :=
  model.WF ∧ Nonempty (Interp model)

/-- Transport integer interpretation evidence across a structure
isomorphism. -/
def Interp.ofIso {left right : Struct intSig} (iso : Struct.Iso left right)
    (interp : Interp left) : Interp right where
  int := fun value => iso.to (interp.int value)
  intTyped := by
    intro value
    exact (iso.inSort intSort (by simp) (interp.int value)).mp
      (interp.intTyped value)
  intInjective := by
    intro first second equal
    have inverse := congrArg iso.inv equal
    have clean : interp.int first = interp.int second := by
      simpa [iso.inv_to] using inverse
    exact interp.intInjective clean
  intExhaustive := by
    intro value typed
    have inverseTyped :
        left.inSort intSort (by simp) (iso.inv value) := by
      have preserved := iso.inSort intSort (by simp) (iso.inv value)
      apply preserved.mpr
      simpa [iso.to_inv] using typed
    rcases interp.intExhaustive (iso.inv value) inverseTyped with
      ⟨integer, equal⟩
    refine ⟨integer, ?_⟩
    have mapped := congrArg iso.to equal
    simpa [iso.to_inv] using mapped
  numeral := by
    intro value
    rw [← iso.literal (.num value) (by rfl), interp.numeral]
  ge := by
    intro leftValue rightValue output
    have preserved := iso.apply (.symb ">=") (by rfl)
      [interp.int leftValue, interp.int rightValue] (iso.inv output)
    simp only [List.map_cons, List.map_nil, iso.to_inv] at preserved
    rw [← preserved]
    rw [interp.ge]
    constructor
    · intro interpreted
      rcases interpreted with ⟨ordered, equal⟩ | ⟨notOrdered, equal⟩
      · left
        exact ⟨ordered, by
          have mapped := congrArg iso.to equal
          simpa [iso.to_inv, iso.bool] using mapped⟩
      · right
        exact ⟨notOrdered, by
          have mapped := congrArg iso.to equal
          simpa [iso.to_inv, iso.bool] using mapped⟩
    · intro interpreted
      rcases interpreted with ⟨ordered, equal⟩ | ⟨notOrdered, equal⟩
      · left
        refine ⟨ordered, ?_⟩
        have mapped := congrArg iso.inv equal
        simpa [iso.inv_to, ← iso.bool] using mapped
      · right
        refine ⟨notOrdered, ?_⟩
        have mapped := congrArg iso.inv equal
        simpa [iso.inv_to, ← iso.bool] using mapped

/-- The integer model predicate is closed under structure isomorphism. -/
theorem models_ofIso {left right : Struct intSig}
    (iso : Struct.Iso left right) (models : Models left) : Models right := by
  rcases models with ⟨wf, ⟨interp⟩⟩
  exact ⟨Struct.WF.ofIso iso wf, ⟨Interp.ofIso iso interp⟩⟩

private theorem intApp_shape {identifier : Ident}
    {argumentSorts : List SSort} {resultSort : SSort}
    (present : intSig.containsIdent identifier = true)
    (inferred : intSig.inferApp? identifier
      (argumentSorts.map some).toArray = some (.ok (some resultSort))) :
    identifier = .symb ">=" ∧
      argumentSorts = [intSort, intSort] ∧ resultSort = boolSort := by
  change intContainsIdent identifier = true at present
  have identifierEq : identifier = .symb ">=" := of_decide_eq_true present
  subst identifier
  refine ⟨rfl, ?_⟩
  change (if intContainsIdent (.symb ">=") then
      some (inferIntApp (.symb ">=") (argumentSorts.map some).toArray)
    else none) = some (.ok (some resultSort)) at inferred
  simp only [intContainsIdent, decide_true, if_true] at inferred
  injection inferred with inferred
  cases argumentSorts with
  | nil =>
      change Except.error _ = Except.ok (some resultSort) at inferred
      contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          change Except.error _ = Except.ok (some resultSort) at inferred
          contradiction
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases firstEq : first = intSort
              · subst first
                by_cases secondEq : second = intSort
                · subst second
                  simp [inferIntApp, requireArity, requireIntArgs,
                    requireArgsOfSort, requireSort] at inferred
                  injection inferred with resultEq
                  exact ⟨rfl, Option.some.inj resultEq.symm⟩
                · simp [inferIntApp, requireArity, requireIntArgs,
                    requireArgsOfSort, requireSort, secondEq]
                    at inferred
                  change Except.error _ = Except.ok _ at inferred
                  contradiction
              · simp [inferIntApp, requireArity, requireIntArgs,
                  requireArgsOfSort, requireSort,
                  firstEq] at inferred
                change Except.error _ = Except.ok _ at inferred
                contradiction
          | cons third rest =>
              change Except.error _ = Except.ok (some resultSort) at inferred
              contradiction

private theorem sig_wf : intSig.WF where
  literalSort := by
    intro literal present
    cases literal with
    | num value => exact intSig_containsSort_int
    | str value | bitvec width value | bool value =>
        simp [intSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  appSorts := by
    intro identifier argumentSorts resultSort inferred
    have present : intSig.containsIdent identifier = true :=
      intSig.inferApp_present identifier
        (argumentSorts.map some).toArray (by rw [inferred]; rfl)
    rcases intApp_shape present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    simp only [Sig.containsSortList_cons, Sig.containsSortList_nil,
      Bool.and_true]
    constructor
    · simp only [intSig_containsSort_int, Bool.true_and]
    · exact intSig_containsSort_bool

/-- Semantic integer theory for the modeled signature. -/
def theory : Crush.Metatheory.SMT.Theory intSig where
  sig_wf := sig_wf
  Models := Models
  models_wf := And.left
  iso_closed := models_ofIso

/-- A well-formed full model with the integer laws has a well-formed integer
reduct. This is the structure-level adequacy theorem used by every concrete
integer realization. -/
theorem reduct_wf (model : Model) (wf : model.WF)
    (interp : Interp (Model.reduct model intSig)) :
    (Model.reduct model intSig).WF where
  sortNonempty := by
    intro sort present
    exact model.sortNonempty sort
  boolTyped := by
    intro present value
    exact model.boolTyped value
  literalSort := by
    intro literal present
    cases literal with
    | num value =>
        change intSig.containsSort intSort = true
        exact intSig_containsSort_int
    | str value | bitvec width value | bool value =>
        simp [intSig, Sig.ofClassifiers, Sig.containsLiteral] at present
  literalTyped := by
    intro literal present
    cases literal with
    | num value => exact model.literalTyped (.num value)
    | str value | bitvec width value | bool value =>
        simp [intSig, Sig.ofClassifiers, Sig.containsLiteral] at present
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    rcases intApp_shape present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    rcases Struct.ValuesTyped.exists_cons typed with
      ⟨first, rest, rfl, firstTyped, restTyped⟩
    rcases Struct.ValuesTyped.exists_cons restTyped with
      ⟨second, tail, rfl, secondTyped, tailTyped⟩
    have tailEq := Struct.ValuesTyped.eq_nil tailTyped
    subst tail
    rcases interp.intExhaustive first firstTyped with ⟨left, rfl⟩
    rcases interp.intExhaustive second secondTyped with ⟨right, rfl⟩
    let output := (Model.reduct model intSig).bool (decide (right ≤ left))
    refine ⟨by simp, output, model.boolTyped _, ?_, ?_⟩
    · by_cases ordered : right ≤ left
      · exact (interp.ge left right output).mpr
          (Or.inl ⟨ordered, by simp [output, ordered]⟩)
      · exact (interp.ge left right output).mpr
          (Or.inr ⟨ordered, by simp [output, ordered]⟩)
    · intro other applied
      exact wf.apply_unique (.symb ">=") [interp.int left, interp.int right]
        other output applied (by
          by_cases ordered : right ≤ left
          · exact (interp.ge left right output).mpr
              (Or.inl ⟨ordered, by simp [output, ordered]⟩)
          · exact (interp.ge left right output).mpr
              (Or.inr ⟨ordered, by simp [output, ordered]⟩))

/-- Package full-model well-formedness and the integer laws as a model of the
integer semantic theory. -/
theorem models (model : Model) (wf : model.WF)
    (interp : Interp (Model.reduct model intSig)) :
    Models (Model.reduct model intSig) :=
  ⟨reduct_wf model wf interp, ⟨interp⟩⟩

/-! ## Concrete integer model -/

private inductive WitnessValue where
  | boolean : Bool → WitnessValue
  | integer : Int → WitnessValue
  | other : SSort → WitnessValue

private def WitnessValue.InSort (sort : SSort) : WitnessValue → Prop
  | .boolean _ => sort = boolSort
  | .integer _ => sort = intSort
  | .other declared =>
      sort = declared ∧ sort ≠ boolSort ∧ sort ≠ intSort

private def witnessLiteral : Literal → WitnessValue
  | .bool value => .boolean value
  | .num value => .integer value
  | .str _ => .other stringSort
  | .bitvec width _ => .other (bitvecSort width)

private def witnessApply (identifier : Ident) (arguments : List WitnessValue)
    (output : WitnessValue) : Prop :=
  ∃ left right : Int,
    identifier = .symb ">=" ∧
    arguments = [.integer left, .integer right] ∧
    output = .boolean (decide (right ≤ left))

private def witness : Model where
  Value := WitnessValue
  inSort := WitnessValue.InSort
  sortNonempty := by
    intro sort
    by_cases boolEq : sort = boolSort
    · exact ⟨.boolean false, boolEq⟩
    by_cases intEq : sort = intSort
    · exact ⟨.integer 0, intEq⟩
    · exact ⟨.other sort, rfl, boolEq, intEq⟩
  bool := .boolean
  boolTyped := by intro value; rfl
  boolInjective := by intro left right equal; injection equal
  literal := witnessLiteral
  literalTyped := by
    intro literal
    cases literal <;>
      simp [witnessLiteral, WitnessValue.InSort,
        Literal.sort, stringSort, boolSort, intSort, bitvecSort]
  apply := witnessApply

private theorem boolSort_ne_intSort : boolSort ≠ intSort := by
  intro equal
  change SSort.app (.symb "Bool") #[] = SSort.app (.symb "Int") #[] at equal
  injection equal with identifiersEqual
  injection identifiersEqual with namesEqual
  exact (by decide : ("Bool" : String) ≠ "Int") namesEqual

private theorem witness_wf : witness.WF where
  bool_exhaustive := by
    intro value typed
    cases value with
    | boolean value => exact ⟨value, rfl⟩
    | integer value => exact False.elim (boolSort_ne_intSort typed)
    | other sort => simp [witness, WitnessValue.InSort] at typed
  apply_unique := by
    intro identifier arguments left right leftApplied rightApplied
    rcases leftApplied with
      ⟨leftArg, rightArg, identifierEq, argumentsEq, leftEq⟩
    rcases rightApplied with
      ⟨otherLeft, otherRight, otherIdentifierEq, otherArgumentsEq, rightEq⟩
    rw [argumentsEq] at otherArgumentsEq
    injection otherArgumentsEq with leftArgEq restEq
    injection restEq with rightArgEq tailEq
    injection leftArgEq with leftIntEq
    injection rightArgEq with rightIntEq
    subst otherLeft
    subst otherRight
    exact leftEq.trans rightEq.symm

private def witnessInterp : Interp (Model.reduct witness intSig) where
  int := .integer
  intTyped := by intro value; rfl
  intInjective := by intro left right equal; injection equal
  intExhaustive := by
    intro value typed
    change WitnessValue at value
    change WitnessValue.InSort intSort value at typed
    change ∃ integer, value = WitnessValue.integer integer
    cases value with
    | boolean value => exact False.elim (boolSort_ne_intSort typed.symm)
    | integer value => exact ⟨value, rfl⟩
    | other sort => simp [WitnessValue.InSort] at typed
  numeral := by intro value; rfl
  ge := by
    intro left right output
    change WitnessValue at output
    change witnessApply (.symb ">=")
        [.integer left, .integer right] output ↔
      (right ≤ left ∧ output = WitnessValue.boolean true) ∨
        (¬right ≤ left ∧ output = WitnessValue.boolean false)
    constructor
    · rintro ⟨actualLeft, actualRight, identifierEq, argumentsEq, outputEq⟩
      injection argumentsEq with leftEq restEq
      injection restEq with rightEq tailEq
      injection leftEq with leftIntEq
      injection rightEq with rightIntEq
      subst actualLeft
      subst actualRight
      by_cases ordered : right ≤ left
      · exact Or.inl ⟨ordered, by simpa [witness, ordered] using outputEq⟩
      · exact Or.inr ⟨ordered, by simpa [witness, ordered] using outputEq⟩
    · intro standardOutput
      refine ⟨left, right, rfl, rfl, ?_⟩
      rcases standardOutput with ⟨ordered, rfl⟩ | ⟨notOrdered, rfl⟩
      · simp [ordered]
      · simp [notOrdered]

/-- The integer theory has a concrete full model, including the mandatory
logical laws. -/
theorem models_exists : ∃ model : Model, model.WF ∧
    Models (Model.reduct model intSig) :=
  ⟨witness, witness_wf, models witness witness_wf witnessInterp⟩

/-- Semantic environment matching the default checker registry. -/
def env : Theory.Env where
  sigEnv := defaultSigEnv
  sig_wf := defaultSigEnv_wf
  decl := by
    rintro ⟨index, bound⟩
    change index < 1 at bound
    have indexEq : index = 0 := by omega
    subst index
    exact theory

/-- One model of the integer reduct is a model of every combination in the
default one-entry registry. The combination may omit Int; supplying its laws
in that case is harmless and keeps realization monotone. -/
theorem combModels (comb : Theory.Comb env) {model : Model}
    (wf : model.WF) (integers : Models (Model.reduct model intSig)) :
    Theory.Comb.Models comb model := by
  refine ⟨wf, ?_⟩
  intro theory active
  rcases theory with ⟨index, bound⟩
  change index < 1 at bound
  have indexEq : index = 0 := by omega
  have theoryEq : (⟨index, bound⟩ : Fin env.sigEnv.modeled.length) =
      intId := Fin.ext indexEq
  rw [theoryEq]
  exact integers

/-- Every combination in the default environment has a concrete model. One
explicit integer model witnesses every requirement set, ruling out an empty
model class at the modular UNSAT boundary. -/
theorem combModels_exists (comb : Theory.Comb env) :
    ∃ model : Model, Theory.Comb.Models comb model :=
  ⟨witness, combModels comb witness_wf
    (models witness witness_wf witnessInterp)⟩

/-- The default registry has one optional theory and no dependencies, so its
closed combination records exactly the generic syntax traversal result. -/
theorem comb_active (commands : Array Command) :
    (Theory.Comb.ofCommands env commands).active intId ↔
      defaultSigEnv.usesCommands commands intId = true := by
  constructor
  · intro active
    cases active with
    | direct used => exact used
    | dependency active member =>
        change _ ∈ [] at member
        contradiction
  · intro used
    exact Theory.Comb.active_of_used (env := env) (commands := commands) used

end Int

namespace Theory

/-- Semantic environment used by the lowering pipeline. It contains
the mandatory logical core and every interpreted theory registered by the
modeled checker. The integer module constructs it while Int is the sole
optional interpreted theory. -/
abbrev defaultEnv : Env := Int.env

end Theory

/-- Default modular UNSAT boundary used by the lowering theorem. The selected
combination is computed from the same registry used by the modeled checker. -/
abbrev CommandsUnsat (commands : Array Crush.SMT.Command) : Prop :=
  Theory.Comb.CommandsUnsat Theory.defaultEnv commands

end Crush.Metatheory.SMT
