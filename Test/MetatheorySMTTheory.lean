import Crush.Metatheory.SMT.IntTheory

/-!
# Modular SMT theory tests

These tests instantiate the general registry with two interpreted theories.
The `Color` theory contributes a sort and `color.rank : Color → Int`, so its
dependency on integer semantics is observable both in syntax checking and in
the command-induced theory combination.
-/

namespace Crush.Metatheory.SMT.MixedTheoryTests

open Crush.SMT
open Crush.SMT.Theory

private abbrev colorSort : SSort := .app (.symb "Color") #[]

private abbrev colorRank : Ident := .symb "color.rank"

@[simp] private def colorSortArity? : Ident → Option Nat
  | .symb "Bool" | .symb "Int" | .symb "Color" => some 0
  | _ => none

private abbrev colorContainsIdent (identifier : Ident) : Bool :=
  decide (identifier = colorRank)

@[simp] private def inferColorApp (identifier : Ident)
    (arguments : Array (Option SSort)) : AppResult := do
  unless identifier = colorRank do
    throw s!"unknown color identifier `{identifier}`"
  requireArity "color.rank" arguments.size 1
  requireSort "argument of `color.rank`" arguments[0]! colorSort
  return some intSort

private abbrev colorSig : Sig := Sig.ofClassifiers colorSortArity?
  colorContainsIdent (fun _ => none) inferColorApp

private theorem core_color_compatible : coreSig.Compatible colorSig := by
  refine {
    sort := ?_
    literal := ?_
    app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [coreSig, colorSig, Sig.ofClassifiers,
            coreSortArity?, colorSortArity?] at leftPresent rightPresent
          omega
        · simp [coreSig, Sig.ofClassifiers,
            coreSortArity?, bool] at leftPresent
    | indexed name indices =>
        simp [coreSig, Sig.ofClassifiers, coreSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;>
      simp [colorSig, Sig.ofClassifiers] at rightPresent
  · intro identifier arguments leftResult rightResult
      leftPresent rightPresent
    have leftIdent := coreSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := colorSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have rightEq : identifier = colorRank :=
      of_decide_eq_true rightIdent
    subst identifier
    simp [coreSig, Sig.ofClassifiers, coreContainsIdent, colorRank] at leftIdent

private theorem core_int_compatible : coreSig.Compatible intSig := by
  refine {
    sort := ?_
    literal := ?_
    app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [coreSig, intSig, Sig.ofClassifiers,
            coreSortArity?, intSortArity?] at leftPresent rightPresent
          omega
        · simp [coreSig, Sig.ofClassifiers,
            coreSortArity?, bool] at leftPresent
    | indexed name indices =>
        simp [coreSig, Sig.ofClassifiers, coreSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;>
      simp [coreSig, intSig, Sig.ofClassifiers] at leftPresent rightPresent
  · intro identifier arguments leftResult rightResult
      leftPresent rightPresent
    have leftIdent := coreSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := intSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have rightEq : identifier = .symb ">=" :=
      of_decide_eq_true rightIdent
    subst identifier
    simp [coreSig, Sig.ofClassifiers, coreContainsIdent] at leftIdent

private theorem int_color_compatible : intSig.Compatible colorSig := by
  refine {
    sort := ?_
    literal := ?_
    app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [intSig, colorSig, Sig.ofClassifiers,
            intSortArity?, coreSortArity?, colorSortArity?] at leftPresent rightPresent
          omega
        · by_cases integer : name = "Int"
          · subst name
            simp [intSig, colorSig, Sig.ofClassifiers,
              intSortArity?, coreSortArity?, colorSortArity?] at leftPresent rightPresent
            omega
          · simp [intSig, Sig.ofClassifiers,
              intSortArity?, coreSortArity?, bool, integer] at leftPresent
    | indexed name indices =>
        simp [intSig, Sig.ofClassifiers,
          intSortArity?, coreSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;>
      simp [colorSig, Sig.ofClassifiers] at rightPresent
  · intro identifier arguments leftResult rightResult
      leftPresent rightPresent
    have leftIdent := intSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := colorSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have leftEq : identifier = .symb ">=" := of_decide_eq_true leftIdent
    have rightEq : identifier = colorRank := of_decide_eq_true rightIdent
    simp [leftEq, colorRank] at rightEq

private abbrev intId : Fin 2 := ⟨0, by omega⟩

private abbrev colorId : Fin 2 := ⟨1, by omega⟩

private theorem id_cases (theory : Fin 2) :
    theory = intId ∨ theory = colorId := by
  rcases theory with ⟨index, bound⟩
  have index_cases : index = 0 ∨ index = 1 := by omega
  cases index_cases with
  | inl equal =>
      left
      apply Fin.ext
      simp [equal]
  | inr equal =>
      right
      apply Fin.ext
      simp [equal]

private abbrev intEntry : Entry where
  key := `Int
  deps := []
  sig := intSig

private abbrev colorEntry : Entry where
  key := `Color
  deps := [`Int]
  sig := colorSig

private abbrev sortProvider (identifier : Ident) : Option (Provider 2 0) :=
  if coreSig.containsSortCtor identifier then some .core
  else if identifier = .symb "Int" then some (.modeled intId)
  else if identifier = .symb "Color" then some (.modeled colorId)
  else none

private abbrev identProvider (identifier : Ident) : Option (Provider 2 0) :=
  if coreSig.containsIdent identifier then some .core
  else if identifier = .symb ">=" then some (.modeled intId)
  else if identifier = colorRank then some (.modeled colorId)
  else none

@[simp] private def literalProvider : Literal → Option (Provider 2 0)
  | .bool _ => some .core
  | .num _ => some (.modeled intId)
  | .str _ | .bitvec _ _ => none

private def deps (theory : Fin 2) : List (Fin 2) :=
  if theory = colorId then [intId] else []

private abbrev sigEnv : SigEnv where
  core := coreSig
  modeled := [intEntry, colorEntry]
  syntaxOnly := []
  sortProvider := sortProvider
  identProvider := identProvider
  literalProvider := literalProvider
  depIds := deps

@[simp] private theorem sigEnv_knownColorSort :
    sigEnv.isKnownSortCtor (.symb "Color") = true := by rfl

@[simp] private theorem sigEnv_modeledColorSort :
    sigEnv.isModeledSortCtor (.symb "Color") = true := by rfl

@[simp] private theorem sigEnv_colorSortArity :
    sigEnv.sortArity? (.symb "Color") = some 0 := by rfl

@[simp] private theorem sigEnv_knownColorRank :
    sigEnv.isKnownIdent colorRank = true := by
  simp [SigEnv.isKnownIdent, sigEnv, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem sigEnv_modeledColorRank :
    sigEnv.isModeledIdent colorRank = true := by
  simp [SigEnv.isModeledIdent,
    identProvider, coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem sigEnv_colorRankApp :
    sigEnv.inferApp? colorRank #[some colorSort] =
      some (.ok (some intSort)) := by
  simp [SigEnv.inferApp?, SigEnv.providerSig, sigEnv, identProvider,
    coreSig, colorSig, Sig.ofClassifiers, coreContainsIdent,
    inferColorApp, requireArity, requireSort,
    Pure.pure, Except.pure]
  rfl

private theorem colorSig_rankApp :
    colorSig.inferApp? colorRank #[some colorSort] =
      some (.ok (some intSort)) := by
  simp [colorSig, Sig.ofClassifiers, colorContainsIdent,
    inferColorApp, requireArity, requireSort]
  rfl

@[simp] private theorem sigEnv_knownEq :
    sigEnv.isKnownIdent (.symb "=") = true := by
  simp [SigEnv.isKnownIdent, sigEnv, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem sigEnv_modeledEq :
    sigEnv.isModeledIdent (.symb "=") = true := by
  simp [SigEnv.isModeledIdent,
    identProvider, coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem sigEnv_eqIntApp :
    sigEnv.inferApp? (.symb "=") #[some intSort, some intSort] =
      some (.ok (some boolSort)) := by
  simp [SigEnv.inferApp?, SigEnv.providerSig, sigEnv, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent, inferCoreApp,
    requireArity, requireSame, Pure.pure, Except.pure]
  rfl

private theorem sigEnv_eqRawIntApp :
    sigEnv.inferApp? (.symb "=")
        #[some (.app (.symb "Int") #[]), some (.app (.symb "Int") #[])] =
      some (.ok (some (.app (.symb "Bool") #[]))) := by
  exact sigEnv_eqIntApp

@[simp] private theorem intDoesNotSelectColorSort :
    sigEnv.usesSort intId colorSort = false := by
  rw [SigEnv.usesSort.eq_2]
  simp [SigEnv.usesSortCtor, SigEnv.usesSortList.eq_1,
    SigEnv.selects, sigEnv, sortProvider, coreSig,
    Sig.containsSortCtor, Sig.ofClassifiers, coreSortArity?]

@[simp] private theorem intDoesNotSelectColorRank :
    sigEnv.usesIdent intId colorRank = false := by
  simp [SigEnv.usesIdent, SigEnv.selects, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem intDoesNotSelectEq :
    sigEnv.usesIdent intId (.symb "=") = false := by
  simp [SigEnv.usesIdent, SigEnv.selects, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

private theorem rankTermsDoNotUseInt :
    sigEnv.usesTerm intId (.symbApp "=" #[
      .app colorRank #[.bvar 0],
      .app colorRank #[.bvar 0]]) = false := by
  unfold Term.symbApp
  rw [SigEnv.usesTerm.eq_3]
  simp [SigEnv.usesTermList.eq_1, SigEnv.usesTermList.eq_2,
    SigEnv.usesTerm.eq_2, SigEnv.usesTerm.eq_3]
  constructor
  · change sigEnv.usesIdent intId (.symb "=") = false
    exact intDoesNotSelectEq
  · change sigEnv.usesIdent intId colorRank = false
    exact intDoesNotSelectColorRank

private theorem sigEnv_wf : sigEnv.WF := by
  refine {
    sort_provider := ?_
    ident_provider := ?_
    literal_provider := ?_
    core_compatible := ?_
    modeled_compatible := ?_
    deps_resolve := ?_
    deps_before := ?_ }
  · intro identifier provider found
    simp only [sigEnv] at found ⊢
    unfold sortProvider at found
    split at found
    next core =>
      injection found with providerEq
      subst provider
      exact core
    next notCore =>
      split at found
      next integer =>
        injection found with providerEq
        subst provider
        simp [SigEnv.providerSig, intEntry, intId,
          intSig, Sig.containsSortCtor, Sig.ofClassifiers,
          intSortArity?, coreSortArity?, integer]
      next notInteger =>
        split at found
        next color =>
          injection found with providerEq
          subst provider
          simp [SigEnv.providerSig, colorEntry, colorId,
            colorSig, Sig.containsSortCtor, Sig.ofClassifiers,
            colorSortArity?, color]
        next notColor => contradiction
  · intro identifier provider found
    simp only [sigEnv] at found ⊢
    unfold identProvider at found
    split at found
    next core =>
      injection found with providerEq
      subst provider
      exact core
    next notCore =>
      split at found
      next integer =>
        injection found with providerEq
        subst provider
        simp [SigEnv.providerSig, intEntry, intId,
          intSig, Sig.ofClassifiers, intContainsIdent, integer]
      next notInteger =>
        split at found
        next color =>
          injection found with providerEq
          subst provider
          simp [SigEnv.providerSig, colorEntry, colorId,
            colorSig, Sig.ofClassifiers, colorContainsIdent, color]
        next notColor => contradiction
  · intro literal provider found
    cases literal with
    | bool value =>
        have providerEq : provider = .core := by
          exact (Option.some.inj found).symm
        subst provider
        rfl
    | num value =>
        have providerEq : provider = .modeled intId := by
          exact (Option.some.inj found).symm
        subst provider
        rfl
    | str value | bitvec width value =>
        simp [sigEnv, literalProvider] at found
  · intro index
    cases id_cases index with
    | inl equal =>
        subst index
        simpa [sigEnv, intId, intEntry] using core_int_compatible
    | inr equal =>
        subst index
        simpa [sigEnv, colorId, colorEntry] using core_color_compatible
  · intro left right
    cases id_cases left with
    | inl leftEq =>
      subst left
      cases id_cases right with
      | inl rightEq =>
        subst right
        simpa [sigEnv, intId, intEntry] using Sig.compatible_refl intSig
      | inr rightEq =>
        subst right
        simpa [sigEnv, intId, colorId, intEntry, colorEntry] using
          int_color_compatible
    | inr leftEq =>
      subst left
      cases id_cases right with
      | inl rightEq =>
        subst right
        simpa [sigEnv, intId, colorId, intEntry, colorEntry] using
          int_color_compatible.symm
      | inr rightEq =>
        subst right
        simpa [sigEnv, colorId, colorEntry] using Sig.compatible_refl colorSig
  · intro theory dependency member
    simp only [sigEnv] at member ⊢
    unfold deps at member
    split at member
    next color =>
      subst theory
      have dependencyEq : dependency = intId := List.mem_singleton.mp member
      subst dependency
      simp [intId, colorId, intEntry, colorEntry]
    next notColor =>
      exact False.elim (List.not_mem_nil member)
  · intro theory dependency member
    simp only [sigEnv] at member
    unfold deps at member
    split at member
    next color =>
      subst theory
      have dependencyEq : dependency = intId := List.mem_singleton.mp member
      subst dependency
      decide
    next notColor =>
      exact False.elim (List.not_mem_nil member)

/-- Closing a Color requirement also selects Int, while an Int requirement
does not select Color. -/
private def closeReqs (requirements : Theory.Reqs sigEnv)
    (theory : Fin sigEnv.modeled.length) : Bool :=
  if theory = intId then
    requirements intId || requirements colorId
  else
    requirements colorId

private def closure : Theory.Closure sigEnv where
  close := closeReqs
  includes := by
    intro requirements theory required
    cases id_cases theory with
    | inl equal =>
        subst theory
        unfold closeReqs
        rw [if_pos rfl]
        simp only [Bool.or_eq_true]
        exact Or.inl required
    | inr equal =>
        subst theory
        unfold closeReqs
        rw [if_neg (by decide)]
        exact required
  deps := by
    intro requirements theory active dependency member
    cases id_cases theory with
    | inl equal =>
        subst theory
        have empty : sigEnv.depIds intId = [] := by
          simp [sigEnv, deps, intId, colorId]
        rw [empty] at member
        exact False.elim (List.not_mem_nil member)
    | inr equal =>
        subst theory
        have dependencyEq : dependency = intId := by
          change dependency ∈ [intId] at member
          exact List.mem_singleton.mp member
        subst dependency
        simp [closeReqs, intId, colorId] at active ⊢
        exact Or.inr active
  least := by
    intro requirements closed includes closedDeps theory active
    cases id_cases theory with
    | inl equal =>
        subst theory
        simp [closeReqs] at active
        cases active with
        | inl required => exact includes intId required
        | inr colorRequired =>
            have colorActive := includes colorId colorRequired
            apply closedDeps colorId colorActive intId
            exact List.mem_singleton.mpr rfl
    | inr equal =>
        subst theory
        apply includes colorId
        simpa [closeReqs, intId, colorId] using active

/-- Color is an uninterpreted-sort theory with a typed, total `rank`
operation. `Struct.WF` states precisely the usual EUF carrier and function
conditions; no equation constrains which integer rank a color receives. -/
private def colorTheory : Crush.Metatheory.SMT.Theory colorSig where
  Models := Struct.WF
  models_wf := id
  iso_closed := Struct.WF.ofIso

private def env : Theory.Env where
  sigEnv := sigEnv
  sig_wf := sigEnv_wf
  decl := by
    intro theory
    by_cases integer : theory = intId
    · subst theory
      exact Int.theory
    · have color : theory = colorId :=
        Or.resolve_left (id_cases theory) integer
      subst theory
      exact colorTheory
  closure := closure

/-- Model-theoretic expansion by the new `color.rank` symbol. The carrier,
sorts, literals, and existing symbols are unchanged; every Color value is sent
to integer zero. -/
private def expandColor (model : Model) (integers : model.IntInterp) : Model where
  Value := model.Value
  inSort := model.inSort
  sortNonempty := model.sortNonempty
  bool := model.bool
  boolTyped := model.boolTyped
  boolInjective := model.boolInjective
  literal := model.literal
  literalTyped := model.literalTyped
  apply := fun identifier values output =>
    if identifier = colorRank then
      ∃ input, values = [input] ∧ model.inSort colorSort input ∧
        output = integers.int 0
    else
      model.apply identifier values output

/-- Integer laws are preserved by the Color expansion because the new symbol
has a distinct identifier. -/
private def expandColorIntegers (model : Model) (integers : model.IntInterp) :
    (expandColor model integers).IntInterp where
  int := integers.int
  int_typed := integers.int_typed
  int_injective := integers.int_injective
  int_exhaustive := integers.int_exhaustive
  numeral := integers.numeral
  ge := by
    intro left right output
    simpa [expandColor] using integers.ge left right output

private theorem expandColor_standard (model : Model)
    (standard : model.Standard) (integers : model.IntInterp) :
    (expandColor model integers).Standard where
  bool_exhaustive := standard.bool_exhaustive
  integer := ⟨expandColorIntegers model integers⟩
  apply_unique := by
    intro identifier values left right leftApplied rightApplied
    change (if identifier = colorRank then _ else _) at leftApplied rightApplied
    by_cases color : identifier = colorRank
    · rw [if_pos color] at leftApplied rightApplied
      rcases leftApplied with ⟨leftInput, leftValues, leftTyped, leftEq⟩
      rcases rightApplied with ⟨rightInput, rightValues, rightTyped, rightEq⟩
      exact leftEq.trans rightEq.symm
    · rw [if_neg color] at leftApplied rightApplied
      exact standard.apply_unique identifier values left right
        leftApplied rightApplied

private theorem colorApp_rank {identifier : Ident}
    {argumentSorts : List SSort} {resultSort : SSort}
    (present : colorSig.containsIdent identifier = true)
    (inferred : colorSig.inferApp? identifier
      (argumentSorts.map some).toArray = some (.ok (some resultSort))) :
    identifier = colorRank ∧ argumentSorts = [colorSort] ∧
      resultSort = intSort := by
  have identifierEq : identifier = colorRank := of_decide_eq_true present
  subst identifier
  refine ⟨rfl, ?_⟩
  cases argumentSorts with
  | nil =>
      simp [colorSig, Sig.ofClassifiers, colorContainsIdent,
        inferColorApp, requireArity] at inferred
      change Except.error _ = Except.ok _ at inferred
      contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          by_cases firstEq : first = colorSort
          · subst first
            simp [colorSig, Sig.ofClassifiers, colorContainsIdent,
              inferColorApp, requireArity, requireSort,
              Pure.pure, Except.pure] at inferred
            injection inferred with resultEq
            exact ⟨rfl, Option.some.inj resultEq.symm⟩
          · simp [colorSig, Sig.ofClassifiers, colorContainsIdent,
              inferColorApp, requireArity, requireSort, firstEq] at inferred
            change Except.error _ = Except.ok _ at inferred
            contradiction
      | cons second tail =>
          simp [colorSig, Sig.ofClassifiers, colorContainsIdent,
            inferColorApp, requireArity] at inferred
          change Except.error _ = Except.ok _ at inferred
          contradiction

/-- The expanded model has a well-formed reduct for Color. This is the EUF
totality proof for `color.rank`; it is independent of any command assertion. -/
private theorem colorReduct_wf (model : Model) (integers : model.IntInterp) :
    (Model.reduct (expandColor model integers) colorSig).WF where
  sortNonempty := by
    intro sort present
    exact model.sortNonempty sort
  boolTyped := by
    intro present value
    exact model.boolTyped value
  literalSort := by
    intro literal present
    simp [colorSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  literalTyped := by
    intro literal present
    simp [colorSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    rcases colorApp_rank present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    rcases Struct.ValuesTyped.exists_cons typed with
      ⟨input, tail, rfl, inputTyped, tailTyped⟩
    have tailEq := Struct.ValuesTyped.eq_nil tailTyped
    subst tail
    refine ⟨by
      simp [colorSig, Sig.containsSort, Sig.ofClassifiers,
        colorSortArity?, intSort], integers.int 0, integers.int_typed 0, ?_, ?_⟩
    · change ∃ value, [input] = [value] ∧
        model.inSort colorSort value ∧ integers.int 0 = integers.int 0
      exact ⟨input, rfl, inputTyped, rfl⟩
    · intro other applied
      change ∃ value, [input] = [value] ∧
        model.inSort colorSort value ∧ other = integers.int 0 at applied
      rcases applied with ⟨otherInput, valuesEq, otherTyped, outputEq⟩
      exact outputEq

/-- One shared full model satisfies every dependency-closed combination of
the Int and Color theories. Thus adding a theory to the combination cannot
make the model class empty by construction. -/
private theorem combModels_exists (comb : Theory.Comb env) :
    ∃ model : Model, Theory.Comb.Models comb model := by
  rcases standardModel_exists with ⟨model, standard⟩
  rcases standard.integer with ⟨integers⟩
  let expanded := expandColor model integers
  have expandedStandard : expanded.Standard :=
    expandColor_standard model standard integers
  refine ⟨expanded, ⟨expandedStandard.wf, ?_⟩⟩
  intro theory active
  cases id_cases theory with
  | inl equal =>
      subst theory
      change Int.theory.Models (Model.reduct expanded intSig)
      unfold Int.theory
      exact Int.ofStandard expandedStandard
  | inr equal =>
      subst theory
      change colorTheory.Models (Model.reduct expanded colorSig)
      unfold colorTheory
      exact colorReduct_wf model integers

private abbrev commands : Array Command := #[
  .assert (.forallE #[("color", colorSort)]
    (.symbApp "=" #[
      .app colorRank #[.bvar 0],
      .app colorRank #[.bvar 0]]))]

/-- The same registry drives checking, so every admitted symbol has a semantic
theory entry. The proof is kernel reduction through the total checker. -/
private theorem commands_wellTyped :
    modeledScriptWellTypedWith sigEnv commands = true := by
  prove_modeled_script_well_typed
  rw [sigEnv_eqRawIntApp]
  simp
  rfl

/-- Requirement traversal selects Color directly from the binder and rank
symbol. -/
private theorem commands_useColor :
    sigEnv.usesCommands commands colorId = true := by
  decide

/-- The syntax itself does not mention an integer literal, integer sort, or
integer operator; Int is selected through Color's declared dependency. -/
private theorem commands_doNotUseIntDirectly :
    sigEnv.usesCommands commands intId = false := by
  simp [SigEnv.usesCommands, SigEnv.usesCommand,
    SigEnv.usesTerm.eq_5]
  constructor
  · change sigEnv.usesSort intId colorSort = false
    exact intDoesNotSelectColorSort
  · change sigEnv.usesTerm intId (.symbApp "=" #[
      .app colorRank #[.bvar 0],
      .app colorRank #[.bvar 0]]) = false
    exact rankTermsDoNotUseInt

private theorem commands_activateColor :
    (Theory.Comb.ofCommands env commands).active colorId = true := by
  exact Theory.Comb.active_of_used commands_useColor

private theorem commands_activateInt :
    (Theory.Comb.ofCommands env commands).active intId = true := by
  change (sigEnv.usesCommands commands intId ||
    sigEnv.usesCommands commands colorId) = true
  rw [commands_doNotUseIntDirectly, commands_useColor]
  rfl

/-- Every model of the induced combination satisfies the reflexive running
example. The proof uses Color's typed-total function law to evaluate `rank`
and the logical evaluator's equality rule. -/
private theorem models_satisfyCommands (model : Model)
    (models : Theory.Comb.Models (Theory.Comb.ofCommands env commands) model) :
    model.SatisfiesCommands commands := by
  have colorModels := models.theory colorId commands_activateColor
  change colorTheory.Models (Model.reduct model colorSig) at colorModels
  unfold colorTheory at colorModels
  intro command member
  simp at member
  subst command
  apply Eval.forallTrue
  intro values typed
  rcases ValuesTyped.exists_cons typed with
    ⟨input, tail, rfl, inputTyped, tailTyped⟩
  have tailEq := ValuesTyped.eq_nil tailTyped
  subst tail
  have structTyped : Struct.ValuesTyped (Model.reduct model colorSig)
      [colorSort] [input] :=
    .cons (by
      simp [colorSig, Sig.containsSort, Sig.ofClassifiers,
        colorSortArity?]) inputTyped .nil
  rcases colorModels.appTyped colorRank (by rfl) [colorSort] intSort
      (by simpa using colorSig_rankApp) [input] structTyped with
    ⟨resultPresent, output, outputTyped, applied, unique⟩
  have rankEval : Eval model [input]
      (.app colorRank #[.bvar 0]) output := by
    apply Eval.symbol (by decide)
    · exact .cons (Eval.bvar rfl) .nil
    · exact applied
  exact Eval.eqTrue rankEval rankEval rfl

/-- The exact mixed-theory command has a model of the exact command-induced
combination, not merely separately inhabited component theories. -/
private theorem commands_haveModel :
    ∃ model : Model,
      Theory.Comb.Models (Theory.Comb.ofCommands env commands) model ∧
        model.SatisfiesCommands commands := by
  rcases combModels_exists (Theory.Comb.ofCommands env commands) with
    ⟨model, models⟩
  exact ⟨model, models, models_satisfyCommands model models⟩

/-- Consequently the modular UNSAT boundary is non-vacuous on the concrete
mixed-theory script. -/
private theorem commands_notUnsat :
    ¬Theory.Comb.CommandsUnsat env commands := by
  intro unsat
  rcases commands_haveModel with ⟨model, models, satisfies⟩
  exact unsat.noModel model models satisfies

end Crush.Metatheory.SMT.MixedTheoryTests
