import Crush.Metatheory.SMT.TheoryEnv

/-!
# Integer theory modeled by the SMT metatheory

This module packages the current integer fragment: the standard integer
carrier, natural-number literals, and `>=`. It deliberately contains no laws
for the syntax-only arithmetic operators.
-/

namespace Crush.Metatheory.SMT.Int

open Crush.SMT
open Crush.SMT.Theory

/-- Interpretation evidence for the current integer signature. -/
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

/-- Models of the current integer theory are well-formed structures carrying
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

private theorem intApp_rank {identifier : Ident}
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
    rcases intApp_rank present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    simp only [Sig.containsSortList_cons, Sig.containsSortList_nil,
      Bool.and_true]
    constructor
    · simp only [intSig_containsSort_int, Bool.true_and]
    · exact intSig_containsSort_bool

/-- Semantic integer theory for the current modeled signature. -/
def theory : Crush.Metatheory.SMT.Theory intSig where
  sig_wf := sig_wf
  Models := Models
  models_wf := And.left
  iso_closed := models_ofIso

/-- The reduct of a standard full model is a well-formed integer structure. -/
private theorem reduct_wf (model : Model) (interp : model.IntInterp)
    (unique : ApplyUnique model) : (Model.reduct model intSig).WF where
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
    rcases intApp_rank present inferred with
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
    rcases interp.int_exhaustive first firstTyped with ⟨left, rfl⟩
    rcases interp.int_exhaustive second secondTyped with ⟨right, rfl⟩
    let output := model.bool (decide (right ≤ left))
    refine ⟨by simp, output, model.boolTyped _, ?_, ?_⟩
    · by_cases ordered : right ≤ left
      · exact (interp.ge left right output).mpr
          (Or.inl ⟨ordered, by simp [output, ordered]⟩)
      · exact (interp.ge left right output).mpr
          (Or.inr ⟨ordered, by simp [output, ordered]⟩)
    · intro other applied
      exact unique (.symb ">=") [interp.int left, interp.int right]
        other output applied (by
          by_cases ordered : right ≤ left
          · exact (interp.ge left right output).mpr
              (Or.inl ⟨ordered, by simp [output, ordered]⟩)
          · exact (interp.ge left right output).mpr
              (Or.inr ⟨ordered, by simp [output, ordered]⟩))

/-- Build the modular integer interpretation from the existing full-model
integer laws. This is the migration bridge; it adds no semantic assumption. -/
def ofModel (model : Model) (interp : model.IntInterp)
    (unique : ApplyUnique model) : Interp (Model.reduct model intSig) where
  int := interp.int
  intTyped := interp.int_typed
  intInjective := interp.int_injective
  intExhaustive := interp.int_exhaustive
  numeral := interp.numeral
  ge := interp.ge

/-- Recover the existing full-model integer evidence from its modular reduct.
The two records state the same laws; this direction is used only during the
compatibility migration. -/
def Interp.toModel {model : Model}
    (interp : Interp (Model.reduct model intSig)) : model.IntInterp where
  int := interp.int
  int_typed := interp.intTyped
  int_injective := interp.intInjective
  int_exhaustive := interp.intExhaustive
  numeral := interp.numeral
  ge := interp.ge

/-- Every existing standard model yields a model of the modular integer
theory. -/
theorem ofStandard {model : Model} (standard : model.Standard) :
    Models (Model.reduct model intSig) := by
  rcases standard.integer with ⟨interp⟩
  exact ⟨reduct_wf model interp standard.apply_unique,
    ⟨ofModel model interp standard.apply_unique⟩⟩

/-- The modular integer theory has a concrete model. -/
theorem models_exists : ∃ model : Model,
    Models (Model.reduct model intSig) := by
  rcases standardModel_exists with ⟨model, standard⟩
  exact ⟨model, ofStandard standard⟩

/-- Dependency closure for the current one-entry registry. The integer theory
has no optional semantic dependency because the logical core is mandatory. -/
private def closure : Theory.Closure currentEnv where
  close := id
  includes := by intros; assumption
  deps := by
    intro requirements theory active dependency member
    change dependency ∈ [] at member
    contradiction
  least := by
    intro requirements closed includes closedDeps theory active
    exact includes theory active

/-- Semantic environment matching the current checker registry. -/
def env : Theory.Env where
  sigEnv := currentEnv
  sig_wf := currentEnv_wf
  decl := by
    rintro ⟨index, bound⟩
    change index < 1 at bound
    have indexEq : index = 0 := by omega
    subst index
    exact theory
  closure := closure

/-- Every combination in the current environment has a concrete model. This
uses one standard model for the logical core and, when selected, its integer
reduct; it therefore rules out vacuity for all current requirement sets. -/
theorem combModels_exists (comb : Theory.Comb env) :
    ∃ model : Model, Theory.Comb.Models comb model := by
  rcases standardModel_exists with ⟨model, standard⟩
  refine ⟨model, ⟨standard.wf, ?_⟩⟩
  rintro ⟨index, bound⟩ active
  change index < 1 at bound
  have indexEq : index = 0 := by omega
  subst index
  exact ofStandard standard

mutual
  /-- For the current one-entry registry, generic sort requirements reproduce
  the legacy integer test. -/
  theorem usesSort_eq : ∀ sort,
      currentEnv.usesSort intId sort = sort.usesInt
    | .bvar index => by
        rw [SigEnv.usesSort.eq_1, SSort.usesInt.eq_def]
    | .app identifier arguments => by
        rw [SigEnv.usesSort.eq_2]
        rw [SigEnv.current_usesSortCtor_int, SSort.usesInt.eq_def]
        cases identifier with
        | symb name =>
            by_cases equal : name = "Int"
            · subst name
              simp
            · simpa [equal] using usesSortList_eq arguments.toList
        | indexed name indices =>
            simpa using usesSortList_eq arguments.toList
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  /-- Generic and legacy integer requirements agree on sort lists. -/
  theorem usesSortList_eq : ∀ sorts,
      currentEnv.usesSortList intId sorts = SSort.listUsesInt sorts
    | [] => by
        rw [SigEnv.usesSortList.eq_1, SSort.listUsesInt.eq_def]
    | sort :: sorts => by
        rw [SigEnv.usesSortList.eq_2]
        rw [SSort.listUsesInt.eq_def, usesSort_eq sort,
          usesSortList_eq sorts]
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

mutual
  /-- Generic and legacy integer requirements agree on terms. -/
  theorem usesTerm_eq : ∀ term,
      currentEnv.usesTerm intId term = term.usesInt
    | .lit literal => by
        rw [SigEnv.usesTerm.eq_1]
        cases literal <;>
          simp [Term.usesInt.eq_def]
    | .bvar index => by
        rw [SigEnv.usesTerm.eq_2, Term.usesInt.eq_def]
    | .app identifier arguments => by
        rw [SigEnv.usesTerm.eq_3]
        rw [SigEnv.current_usesIdent_int]
        cases identifier with
        | symb name =>
            by_cases equal : name = ">="
            · subst name
              rw [Term.usesInt_app_integerComparison]
              simp [intContainsIdent]
            · rw [Term.usesInt_app_of_ne _ _ (by simp [equal])]
              simpa [intContainsIdent, equal] using
                usesTermList_eq arguments.toList
        | indexed name indices =>
            rw [Term.usesInt_app_of_ne _ _ (by simp)]
            simpa [intContainsIdent] using usesTermList_eq arguments.toList
    | .letE bindings body => by
        rw [SigEnv.usesTerm.eq_4]
        rw [Term.usesInt.eq_def, usesBindingList_eq bindings.toList,
          usesTerm_eq body]
    | .forallE binders body => by
        rw [SigEnv.usesTerm.eq_5]
        rw [Term.usesInt.eq_def,
          usesSortList_eq (binders.toList.map (fun binder => binder.2)),
          usesTerm_eq body]
    | .existsE binders body => by
        rw [SigEnv.usesTerm.eq_6]
        rw [Term.usesInt.eq_def,
          usesSortList_eq (binders.toList.map (fun binder => binder.2)),
          usesTerm_eq body]
    | .lam binders body => by
        rw [SigEnv.usesTerm.eq_7]
        rw [Term.usesInt.eq_def,
          usesSortList_eq (binders.toList.map (fun binder => binder.2)),
          usesTerm_eq body]
    | .annot body attributes => by
        rw [SigEnv.usesTerm.eq_8]
        rw [Term.usesInt.eq_def, usesTerm_eq body]
  termination_by term => term.structuralSize
  decreasing_by all_goals simp [Term.structuralSize] <;> omega

  /-- Generic and legacy integer requirements agree on term lists. -/
  theorem usesTermList_eq : ∀ terms,
      currentEnv.usesTermList intId terms = Term.listUsesInt terms
    | [] => by
        rw [SigEnv.usesTermList.eq_1, Term.listUsesInt.eq_def]
    | term :: terms => by
        rw [SigEnv.usesTermList.eq_2]
        rw [Term.listUsesInt.eq_def,
          usesTerm_eq term, usesTermList_eq terms]
  termination_by terms => Term.listStructuralSize terms
  decreasing_by all_goals simp [Term.listStructuralSize] <;> omega

  /-- Generic and legacy integer requirements agree on `let` bindings. -/
  theorem usesBindingList_eq : ∀ bindings,
      currentEnv.usesBindingList intId bindings =
        Term.bindingListUsesInt bindings
    | [] => by
        rw [SigEnv.usesBindingList.eq_1, Term.bindingListUsesInt.eq_def]
    | (_, term) :: bindings => by
        rw [SigEnv.usesBindingList.eq_2]
        rw [Term.bindingListUsesInt.eq_def,
          usesTerm_eq term, usesBindingList_eq bindings]
  termination_by bindings => Term.bindingListStructuralSize bindings
  decreasing_by all_goals simp [Term.bindingListStructuralSize] <;> omega
end

theorem usesFunDef_eq (definition : FunDef) :
    currentEnv.usesFunDef intId definition = definition.usesInt := by
  simp [SigEnv.usesFunDef, FunDef.usesInt, usesSortList_eq, usesSort_eq,
    usesTerm_eq]

theorem usesCtor_eq (constructor : CtorDecl) :
    currentEnv.usesCtor intId constructor = constructor.usesInt := by
  simp [SigEnv.usesCtor, CtorDecl.usesInt, usesSortList_eq]

theorem usesDatatype_eq (datatype : DatatypeDecl) :
    currentEnv.usesDatatype intId datatype = datatype.usesInt := by
  simp [SigEnv.usesDatatype, DatatypeDecl.usesInt, usesCtor_eq]

theorem usesCommand_eq (command : Command) :
    currentEnv.usesCommand intId command = command.usesInt := by
  cases command <;>
    simp [SigEnv.usesCommand, Command.usesInt, usesSortList_eq, usesSort_eq,
      usesTerm_eq, usesFunDef_eq]

/-- The command-induced integer member is exactly the legacy integer
requirement. This theorem is the faithfulness certificate for replacing the
integer-specific traversal. -/
theorem usesCommands_eq (commands : Array Command) :
    currentEnv.usesCommands commands intId = CommandsUseInt commands := by
  simp [SigEnv.usesCommands, CommandsUseInt, usesCommand_eq]

/-- Dependency closure does not change the current integer requirement because
the integer entry has no optional dependencies. -/
theorem comb_int (commands : Array Command) :
    (Theory.Comb.ofCommands env commands).active intId =
      CommandsUseInt commands := by
  simpa [Theory.Comb.ofCommands, Theory.Comb.close, env, closure] using
    usesCommands_eq commands

/-- Command-indexed standardness and the modular command-induced model class
coincide for the current registry. -/
theorem combModels_iff_standardFor (commands : Array Command) (model : Model) :
    Theory.Comb.Models (Theory.Comb.ofCommands env commands) model ↔
      model.StandardFor commands := by
  constructor
  · intro models
    refine {
      bool_exhaustive := models.wf.bool_exhaustive
      integer := ?_
      apply_unique := models.wf.apply_unique }
    intro required
    have active :
        (Theory.Comb.ofCommands env commands).active intId = true := by
      rw [comb_int]
      exact required
    have intModels := models.theory intId active
    rcases intModels.2 with ⟨interp⟩
    exact ⟨interp.toModel⟩
  · intro standard
    refine ⟨standard.wf, ?_⟩
    rintro ⟨index, bound⟩ active
    change index < 1 at bound
    have indexEq : index = 0 := by omega
    subst index
    have required : CommandsUseInt commands = true := by
      rw [← comb_int commands]
      exact active
    rcases standard.integer required with ⟨interp⟩
    exact ⟨reduct_wf model interp standard.apply_unique,
      ⟨ofModel model interp standard.apply_unique⟩⟩

/-- The new modular unsatisfiability boundary is propositionally equivalent to
the existing one for the current registry. -/
theorem commandsUnsat_iff (commands : Array Command) :
    Theory.Comb.CommandsUnsat env commands ↔ CommandsUnsat commands := by
  constructor
  · intro unsat
    exact {
      inFragment := unsat.inFragment
      wellTyped := unsat.wellTyped
      noModel := by
        intro model standard
        exact unsat.noModel model
          ((combModels_iff_standardFor commands model).mpr standard) }
  · intro unsat
    exact {
      inFragment := unsat.inFragment
      wellTyped := unsat.wellTyped
      noModel := by
        intro model models
        exact unsat.noModel model
          ((combModels_iff_standardFor commands model).mp models) }

end Int

/-- Default modular UNSAT boundary used by the lowering theorem. The selected
combination is computed from the same registry used by the modeled checker. -/
abbrev CommandsUnsat (commands : Array Crush.SMT.Command) : Prop :=
  Theory.Comb.CommandsUnsat Int.env commands

/-- Compatibility theorem retained while downstream proofs migrate away from
the integer-specific command boundary. -/
theorem commandsUnsat_iff_legacy (commands : Array Crush.SMT.Command) :
    CommandsUnsat commands ↔ Crush.SMT.CommandsUnsat commands :=
  Int.commandsUnsat_iff commands

end Crush.Metatheory.SMT
