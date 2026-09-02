import Crush.Metatheory.SMT.Int
import Crush.Metatheory.SMT.ModelExt

/-!
# Modular SMT theory tests

These tests instantiate the general registry with three interpreted theories.
The `Color` theory contributes a sort and `color.rank : Color → Int`; the
`Box` theory contributes `Box Color` and `box.get : Box Color → Color`.
Nested sorts and Color's integer dependency therefore exercise an actual
three-way command-induced combination.
-/

namespace Crush.Metatheory.SMT.MixedTheoryTests

open Crush.SMT
open Crush.SMT.Theory

private abbrev RelModel := Crush.SMT.Model

/-! ## Composable fixed-carrier model extensions -/

private def falseExt (model : RelModel) : ModelExt model.Value where
  literal? := fun
    | .bool false => some (model.bool false)
    | _ => none
  apply := fun _ _ _ => False

private def trueExt (model : RelModel) : ModelExt model.Value where
  literal? := fun
    | .bool true => some (model.bool true)
    | _ => none
  apply := fun _ _ _ => False

private theorem falseExt_wf (model : RelModel) :
    (falseExt model).WF model where
  literal_typed := by
    intro literal value present
    cases literal with
    | bool boolean =>
        cases boolean <;> simp [falseExt] at present
        subst value
        exact model.boolTyped false
    | num number | str string | bitvec width number =>
        simp [falseExt] at present
  apply_unique := by simp [falseExt]
  base_agree := by simp [falseExt]

private theorem trueExt_wf (model : RelModel) :
    (trueExt model).WF model where
  literal_typed := by
    intro literal value present
    cases literal with
    | bool boolean =>
        cases boolean <;> simp [trueExt] at present
        subst value
        exact model.boolTyped true
    | num number | str string | bitvec width number =>
        simp [trueExt] at present
  apply_unique := by simp [trueExt]
  base_agree := by simp [trueExt]

private theorem boolExt_disjoint (model : RelModel) :
    (falseExt model).Disjoint (trueExt model) where
  literal := by
    intro literal falseValue trueValue falsePresent truePresent
    cases literal with
    | bool boolean => cases boolean <;> simp [falseExt, trueExt] at falsePresent truePresent
    | num number | str string | bitvec width number =>
        simp [falseExt] at falsePresent
  apply := by simp [falseExt]

private theorem boolExt_inactiveOnInt (model : RelModel) :
    ((falseExt model).union (trueExt model)).InactiveOn intSig where
  literal := by
    intro literal present
    cases literal <;>
      simp [intSig, Sig.ofClassifiers, Sig.containsLiteral,
        falseExt, trueExt] at present ⊢
  apply := by simp [falseExt, trueExt, ModelExt.union]

/-- Two nonempty, disjoint literal contributions combine over one carrier and
preserve the already established integer theory. This is a concrete witness
that extension union and its preservation theorem do not rely on an empty
model class. -/
private theorem modelExt_union_hasIntModel :
    ∃ model : RelModel,
      model.WF ∧ Int.Models (Model.reduct model intSig) := by
  rcases Int.models_exists with ⟨base, witness⟩
  rcases witness with ⟨baseWF, integers⟩
  let ext := (falseExt base).union (trueExt base)
  have extWF : ext.WF base := ModelExt.WF.union
    (falseExt_wf base) (trueExt_wf base) (boolExt_disjoint base)
  have inactive : ext.InactiveOn intSig := boolExt_inactiveOnInt base
  refine ⟨base.withExt ext extWF.toLiteralWF,
    baseWF.withExt extWF, ?_⟩
  exact ModelExt.theory extWF.toLiteralWF inactive Int.theory
    integers

private abbrev colorSort : SSort := .app (.symb "Color") #[]

private abbrev colorRank : Ident := .symb "color.rank"

@[simp] private def colorSortArity? (identifier : Ident) : Option Nat :=
  if identifier = .symb "Bool" then some 0
  else if identifier = .symb "Int" then some 0
  else if identifier = .symb "Color" then some 0
  else none

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

private abbrev boxSort : SSort :=
  .app (.symb "Box") #[colorSort]

private abbrev boxGet : Ident := .symb "box.get"

@[simp] private def boxSortArity? (identifier : Ident) : Option Nat :=
  if identifier = .symb "Bool" then some 0
  else if identifier = .symb "Color" then some 0
  else if identifier = .symb "Box" then some 1
  else none

private abbrev boxContainsIdent (identifier : Ident) : Bool :=
  decide (identifier = boxGet)

@[simp] private def inferBoxApp (identifier : Ident)
    (arguments : Array (Option SSort)) : AppResult := do
  unless identifier = boxGet do
    throw s!"unknown box identifier `{identifier}`"
  requireArity "box.get" arguments.size 1
  requireSort "argument of `box.get`" arguments[0]! boxSort
  return some colorSort

private abbrev boxSig : Sig := Sig.ofClassifiers boxSortArity?
  boxContainsIdent (fun _ => none) inferBoxApp

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

private theorem core_box_compatible : coreSig.Compatible boxSig := by
  refine { sort := ?_, literal := ?_, app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [coreSig, boxSig, Sig.ofClassifiers,
            coreSortArity?, boxSortArity?] at leftPresent rightPresent
          omega
        · simp [coreSig, Sig.ofClassifiers,
            coreSortArity?, bool] at leftPresent
    | indexed name indices =>
        simp [coreSig, Sig.ofClassifiers, coreSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;> simp [boxSig, Sig.ofClassifiers] at rightPresent
  · intro identifier arguments leftResult rightResult leftPresent rightPresent
    have leftIdent := coreSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := boxSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have rightEq : identifier = boxGet := of_decide_eq_true rightIdent
    subst identifier
    simp [coreSig, Sig.ofClassifiers, coreContainsIdent, boxGet] at leftIdent

private theorem int_box_compatible : intSig.Compatible boxSig := by
  refine { sort := ?_, literal := ?_, app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [intSig, boxSig, Sig.ofClassifiers,
            intSortArity?, coreSortArity?, boxSortArity?]
              at leftPresent rightPresent
          omega
        · by_cases integer : name = "Int"
          · subst name
            simp [boxSig, Sig.ofClassifiers, boxSortArity?] at rightPresent
          · simp [intSig, Sig.ofClassifiers,
              intSortArity?, coreSortArity?, bool, integer] at leftPresent
    | indexed name indices =>
        simp [intSig, Sig.ofClassifiers,
          intSortArity?, coreSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;> simp [boxSig, Sig.ofClassifiers] at rightPresent
  · intro identifier arguments leftResult rightResult leftPresent rightPresent
    have leftIdent := intSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := boxSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have leftEq : identifier = .symb ">=" := of_decide_eq_true leftIdent
    have rightEq : identifier = boxGet := of_decide_eq_true rightIdent
    simp [leftEq, boxGet] at rightEq

private theorem color_box_compatible : colorSig.Compatible boxSig := by
  refine { sort := ?_, literal := ?_, app := ?_ }
  · intro identifier leftArity rightArity leftPresent rightPresent
    cases identifier with
    | symb name =>
        by_cases bool : name = "Bool"
        · subst name
          simp [colorSig, boxSig, Sig.ofClassifiers,
            colorSortArity?, boxSortArity?] at leftPresent rightPresent
          omega
        · by_cases color : name = "Color"
          · subst name
            simp [colorSig, boxSig, Sig.ofClassifiers,
              colorSortArity?, boxSortArity?] at leftPresent rightPresent
            omega
          · by_cases integer : name = "Int"
            · subst name
              simp [boxSig, Sig.ofClassifiers, boxSortArity?] at rightPresent
            · simp [colorSig, Sig.ofClassifiers,
                colorSortArity?, bool, integer, color] at leftPresent
    | indexed name indices =>
        simp [colorSig, Sig.ofClassifiers, colorSortArity?] at leftPresent
  · intro literal leftSort rightSort leftPresent rightPresent
    cases literal <;> simp [boxSig, Sig.ofClassifiers] at rightPresent
  · intro identifier arguments leftResult rightResult leftPresent rightPresent
    have leftIdent := colorSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have rightIdent := boxSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have leftEq : identifier = colorRank := of_decide_eq_true leftIdent
    have rightEq : identifier = boxGet := of_decide_eq_true rightIdent
    simp [leftEq, colorRank, boxGet] at rightEq

private abbrev intId : Fin 3 := ⟨0, by omega⟩

private abbrev colorId : Fin 3 := ⟨1, by omega⟩

private abbrev boxId : Fin 3 := ⟨2, by omega⟩

private theorem id_cases (theory : Fin 3) :
    theory = intId ∨ theory = colorId ∨ theory = boxId := by
  rcases theory with ⟨index, bound⟩
  have index_cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  cases index_cases with
  | inl equal =>
      left
      apply Fin.ext
      simp [equal]
  | inr rest =>
      cases rest with
      | inl equal =>
          right
          left
          apply Fin.ext
          simp [equal]
      | inr equal =>
          right
          right
          apply Fin.ext
          simp [equal]

private abbrev intEntry : Entry where
  name := `Int
  sig := intSig

private abbrev colorEntry : Entry where
  name := `Color
  sig := colorSig

private abbrev boxEntry : Entry where
  name := `Box
  sig := boxSig

private abbrev sortProvider (identifier : Ident) : Option (Provider 3 0) :=
  if coreSig.containsSortCtor identifier then some .core
  else if identifier = .symb "Int" then some (.modeled intId)
  else if identifier = .symb "Color" then some (.modeled colorId)
  else if identifier = .symb "Box" then some (.modeled boxId)
  else none

private abbrev identProvider (identifier : Ident) : Option (Provider 3 0) :=
  if coreSig.containsIdent identifier then some .core
  else if identifier = .symb ">=" then some (.modeled intId)
  else if identifier = colorRank then some (.modeled colorId)
  else if identifier = boxGet then some (.modeled boxId)
  else none

@[simp] private def literalProvider : Literal → Option (Provider 3 0)
  | .bool _ => some .core
  | .num _ => some (.modeled intId)
  | .str _ | .bitvec _ _ => none

private def deps (theory : Fin 3) : List (Fin 3) :=
  if theory = colorId then [intId]
  else if theory = boxId then [colorId]
  else []

private abbrev sigEnv : SigEnv where
  core := coreSig
  modeled := [intEntry, colorEntry, boxEntry]
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

@[simp] private theorem sigEnv_knownBoxSort :
    sigEnv.isKnownSortCtor (.symb "Box") = true := by rfl

@[simp] private theorem sigEnv_modeledBoxSort :
    sigEnv.isModeledSortCtor (.symb "Box") = true := by rfl

@[simp] private theorem sigEnv_boxSortArity :
    sigEnv.sortArity? (.symb "Box") = some 1 := by rfl

@[simp] private theorem sigEnv_knownBoxGet :
    sigEnv.isKnownIdent boxGet = true := by
  simp [SigEnv.isKnownIdent, sigEnv, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

@[simp] private theorem sigEnv_modeledBoxGet :
    sigEnv.isModeledIdent boxGet = true := by
  simp [SigEnv.isModeledIdent, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

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

@[simp] private theorem sigEnv_boxGetApp :
    sigEnv.inferApp? boxGet #[some boxSort] =
      some (.ok (some colorSort)) := by
  simp [SigEnv.inferApp?, SigEnv.providerSig, sigEnv, identProvider,
    coreSig, boxSig, Sig.ofClassifiers, coreContainsIdent,
    inferBoxApp, requireArity, requireSort,
    Pure.pure, Except.pure]
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

private theorem sortProvider_modeled {identifier dependency}
    (provided : sortProvider identifier = some (.modeled dependency)) :
    (identifier = .symb "Int" ∧ dependency = intId) ∨
    (identifier = .symb "Color" ∧ dependency = colorId) ∨
    (identifier = .symb "Box" ∧ dependency = boxId) := by
  unfold sortProvider at provided
  split at provided
  next core => simp at provided
  next notCore =>
    split at provided
    next integer =>
      have dependencyEq : intId = dependency := by simpa using provided
      exact Or.inl ⟨integer, dependencyEq.symm⟩
    next notInteger =>
      split at provided
      next color =>
        have dependencyEq : colorId = dependency := by simpa using provided
        exact Or.inr (Or.inl ⟨color, dependencyEq.symm⟩)
      next notColor =>
        split at provided
        next box =>
          have dependencyEq : boxId = dependency := by simpa using provided
          exact Or.inr (Or.inr ⟨box, dependencyEq.symm⟩)
        next notBox => simp at provided

private theorem identProvider_modeled {identifier dependency}
    (provided : identProvider identifier = some (.modeled dependency)) :
    (identifier = .symb ">=" ∧ dependency = intId) ∨
    (identifier = colorRank ∧ dependency = colorId) ∨
    (identifier = boxGet ∧ dependency = boxId) := by
  unfold identProvider at provided
  split at provided
  next core => simp at provided
  next notCore =>
    split at provided
    next integer =>
      have dependencyEq : intId = dependency := by simpa using provided
      exact Or.inl ⟨integer, dependencyEq.symm⟩
    next notInteger =>
      split at provided
      next color =>
        have dependencyEq : colorId = dependency := by simpa using provided
        exact Or.inr (Or.inl ⟨color, dependencyEq.symm⟩)
      next notColor =>
        split at provided
        next box =>
          have dependencyEq : boxId = dependency := by simpa using provided
          exact Or.inr (Or.inr ⟨box, dependencyEq.symm⟩)
        next notBox => simp at provided

private theorem literalProvider_modeled {literal dependency}
    (provided : literalProvider literal = some (.modeled dependency)) :
    dependency = intId := by
  cases literal with
  | num value =>
      have dependencyEq : intId = dependency := by simpa using provided
      exact dependencyEq.symm
  | bool value | str value | bitvec width value => simp at provided

private theorem sigEnv_wf : sigEnv.WF := by
  refine {
    core_eq := rfl
    core_sort := ?_
    core_ident := ?_
    core_literal := ?_
    sort_provider := ?_
    ident_provider := ?_
    literal_provider := ?_
    core_compatible := ?_
    modeled_compatible := ?_
    sort_complete := ?_
    ident_complete := ?_
    literal_complete := ?_
    sort_deps := ?_
    ident_deps := ?_
    literal_deps := ?_ }
  · intro identifier present
    simp [sigEnv, sortProvider, present]
  · intro identifier present
    simp [sigEnv, identProvider, present]
  · intro literal present
    cases literal <;>
      simp [coreSig, Sig.containsLiteral, Sig.ofClassifiers,
        sigEnv, literalProvider] at present ⊢
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
        next notColor =>
          split at found
          next box =>
            injection found with providerEq
            subst provider
            simp [SigEnv.providerSig, boxEntry, boxId,
              boxSig, Sig.containsSortCtor, Sig.ofClassifiers,
              boxSortArity?, box]
          next notBox => contradiction
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
        next notColor =>
          split at found
          next box =>
            injection found with providerEq
            subst provider
            simp [SigEnv.providerSig, boxEntry, boxId,
              boxSig, Sig.ofClassifiers, boxContainsIdent, box]
          next notBox => contradiction
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
    | inr rest =>
        cases rest with
        | inl equal =>
            subst index
            simpa [sigEnv, colorId, colorEntry] using core_color_compatible
        | inr equal =>
            subst index
            simpa [sigEnv, boxId, boxEntry] using core_box_compatible
  · intro left right
    cases id_cases left with
    | inl leftEq =>
        subst left
        cases id_cases right with
        | inl rightEq =>
            subst right
            simpa [sigEnv, intId, intEntry] using Sig.compatible_refl intSig
        | inr rightRest =>
            cases rightRest with
            | inl rightEq =>
                subst right
                simpa [sigEnv, intId, colorId, intEntry, colorEntry] using
                  int_color_compatible
            | inr rightEq =>
                subst right
                simpa [sigEnv, intId, boxId, intEntry, boxEntry] using
                  int_box_compatible
    | inr leftRest =>
        cases leftRest with
        | inl leftEq =>
            subst left
            cases id_cases right with
            | inl rightEq =>
                subst right
                simpa [sigEnv, intId, colorId, intEntry, colorEntry] using
                  int_color_compatible.symm
            | inr rightRest =>
                cases rightRest with
                | inl rightEq =>
                    subst right
                    simpa [sigEnv, colorId, colorEntry] using
                      Sig.compatible_refl colorSig
                | inr rightEq =>
                    subst right
                    simpa [sigEnv, colorId, boxId, colorEntry, boxEntry] using
                      color_box_compatible
        | inr leftEq =>
            subst left
            cases id_cases right with
            | inl rightEq =>
                subst right
                simpa [sigEnv, intId, boxId, intEntry, boxEntry] using
                  int_box_compatible.symm
            | inr rightRest =>
                cases rightRest with
                | inl rightEq =>
                    subst right
                    simpa [sigEnv, colorId, boxId, colorEntry, boxEntry] using
                      color_box_compatible.symm
                | inr rightEq =>
                    subst right
                    simpa [sigEnv, boxId, boxEntry] using
                      Sig.compatible_refl boxSig
  · intro theory identifier present
    rcases id_cases theory with rfl | rfl | rfl
    · change intSig.containsSortCtor identifier = true at present
      cases identifier with
      | indexed name indices =>
          simp [intSig, Sig.containsSortCtor, Sig.ofClassifiers,
            intSortArity?, coreSortArity?] at present
      | symb name =>
          by_cases boolean : name = "Bool"
          · subst name
            exact ⟨.core, rfl, rfl⟩
          · have integer : name = "Int" := by
              simpa [intSig, Sig.containsSortCtor, Sig.ofClassifiers,
                intSortArity?, coreSortArity?, boolean] using present
            subst name
            exact ⟨.modeled intId, rfl, rfl⟩
    · change colorSig.containsSortCtor identifier = true at present
      cases identifier with
      | indexed name indices =>
          simp [colorSig, Sig.containsSortCtor, Sig.ofClassifiers,
            colorSortArity?] at present
      | symb name =>
          by_cases boolean : name = "Bool"
          · subst name
            exact ⟨.core, rfl, rfl⟩
          · by_cases integer : name = "Int"
            · subst name
              exact ⟨.modeled intId, rfl, rfl⟩
            · have color : name = "Color" := by
                simpa [colorSig, Sig.containsSortCtor, Sig.ofClassifiers,
                  colorSortArity?, boolean, integer] using present
              subst name
              exact ⟨.modeled colorId, rfl, rfl⟩
    · change boxSig.containsSortCtor identifier = true at present
      cases identifier with
      | indexed name indices =>
          simp [boxSig, Sig.containsSortCtor, Sig.ofClassifiers,
            boxSortArity?] at present
      | symb name =>
          by_cases boolean : name = "Bool"
          · subst name
            exact ⟨.core, rfl, rfl⟩
          · by_cases color : name = "Color"
            · subst name
              exact ⟨.modeled colorId, rfl, rfl⟩
            · have box : name = "Box" := by
                simpa [boxSig, Sig.containsSortCtor, Sig.ofClassifiers,
                  boxSortArity?, boolean, color] using present
              subst name
              exact ⟨.modeled boxId, rfl, rfl⟩
  · intro theory identifier present
    rcases id_cases theory with rfl | rfl | rfl
    · change intContainsIdent identifier = true at present
      have equal : identifier = .symb ">=" := of_decide_eq_true present
      subst identifier
      exact ⟨.modeled intId, by
        simp [sigEnv, identProvider, coreSig, Sig.ofClassifiers,
          coreContainsIdent, intId], rfl⟩
    · change colorContainsIdent identifier = true at present
      have equal : identifier = colorRank := of_decide_eq_true present
      subst identifier
      exact ⟨.modeled colorId, by
        simp [sigEnv, identProvider, coreSig, Sig.ofClassifiers,
          coreContainsIdent, colorRank, colorId], rfl⟩
    · change boxContainsIdent identifier = true at present
      have equal : identifier = boxGet := of_decide_eq_true present
      subst identifier
      exact ⟨.modeled boxId, by
        simp [sigEnv, identProvider, coreSig, Sig.ofClassifiers,
          coreContainsIdent, boxGet, boxId], rfl⟩
  · intro theory literal present
    rcases id_cases theory with rfl | rfl | rfl
    · change intSig.containsLiteral literal = true at present
      cases literal with
      | num value => exact ⟨.modeled intId, rfl, rfl⟩
      | bool value | str value | bitvec width value =>
          simp [intSig, Sig.containsLiteral, Sig.ofClassifiers] at present
    · change colorSig.containsLiteral literal = true at present
      simp [colorSig, Sig.containsLiteral, Sig.ofClassifiers] at present
    · change boxSig.containsLiteral literal = true at present
      simp [boxSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  · intro theory identifier dependency present provided different
    rcases sortProvider_modeled provided with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases id_cases theory with rfl | rfl | rfl
      · exact False.elim (different rfl)
      · simp [sigEnv, deps, colorId]
      · simp [sigEnv, boxEntry, boxId, boxSig,
          Sig.containsSortCtor, Sig.ofClassifiers, boxSortArity?] at present
    · rcases id_cases theory with rfl | rfl | rfl
      · simp [sigEnv, intEntry, intId, intSig,
          Sig.containsSortCtor, Sig.ofClassifiers,
          intSortArity?, coreSortArity?] at present
      · exact False.elim (different rfl)
      · simp [sigEnv, deps, boxId]
    · rcases id_cases theory with rfl | rfl | rfl
      · simp [sigEnv, intEntry, intId, intSig,
          Sig.containsSortCtor, Sig.ofClassifiers,
          intSortArity?, coreSortArity?] at present
      · simp [sigEnv, colorEntry, colorId, colorSig,
          Sig.containsSortCtor, Sig.ofClassifiers, colorSortArity?] at present
      · exact False.elim (different rfl)
  · intro theory identifier dependency present provided different
    rcases identProvider_modeled provided with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases id_cases theory with rfl | rfl | rfl
      · exact False.elim (different rfl)
      · simp [sigEnv, colorEntry, colorId, colorSig,
          Sig.ofClassifiers, colorContainsIdent, colorRank] at present
      · simp [sigEnv, boxEntry, boxId, boxSig,
          Sig.ofClassifiers, boxContainsIdent, boxGet] at present
    · rcases id_cases theory with rfl | rfl | rfl
      · simp [sigEnv, intEntry, intId, intSig,
          Sig.ofClassifiers, intContainsIdent, colorRank] at present
      · exact False.elim (different rfl)
      · simp [sigEnv, boxEntry, boxId, boxSig,
          Sig.ofClassifiers, boxContainsIdent, colorRank, boxGet] at present
    · rcases id_cases theory with rfl | rfl | rfl
      · simp [sigEnv, intEntry, intId, intSig,
          Sig.ofClassifiers, intContainsIdent, boxGet] at present
      · simp [sigEnv, colorEntry, colorId, colorSig,
          Sig.ofClassifiers, colorContainsIdent, colorRank, boxGet] at present
      · exact False.elim (different rfl)
  · intro theory literal dependency present provided different
    have dependencyEq := literalProvider_modeled provided
    subst dependency
    rcases id_cases theory with rfl | rfl | rfl
    · exact False.elim (different rfl)
    · cases literal <;>
        simp [sigEnv, colorEntry, colorId, colorSig,
          Sig.containsLiteral, Sig.ofClassifiers] at present
    · cases literal <;>
        simp [sigEnv, boxEntry, boxId, boxSig,
          Sig.containsLiteral, Sig.ofClassifiers] at present

/-- Model-theoretic expansion by the new `color.rank` symbol. The carrier,
sorts, literals, and existing symbols are unchanged; every Color value is sent
to integer zero. -/
private def expandColor (model : RelModel)
    (integers : Int.Interp (Model.reduct model intSig)) : RelModel where
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
private def expandColorIntegers (model : RelModel)
    (integers : Int.Interp (Model.reduct model intSig)) :
    Int.Interp (Model.reduct (expandColor model integers) intSig) where
  int := integers.int
  intTyped := integers.intTyped
  intInjective := integers.intInjective
  intExhaustive := integers.intExhaustive
  numeral := integers.numeral
  ge := by
    intro left right output
    change model.Value at output
    have law := integers.ge left right output
    change model.apply (.symb ">=")
        [integers.int left, integers.int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false) at law
    change (expandColor model integers).apply (.symb ">=")
        [integers.int left, integers.int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false)
    simpa [expandColor, colorRank] using law

private theorem expandColor_wf (model : RelModel) (wf : model.WF)
    (integers : Int.Interp (Model.reduct model intSig)) :
    (expandColor model integers).WF where
  bool_exhaustive := wf.bool_exhaustive
  apply_unique := by
    intro identifier values left right leftApplied rightApplied
    change (if identifier = colorRank then _ else _) at leftApplied rightApplied
    by_cases color : identifier = colorRank
    · rw [if_pos color] at leftApplied rightApplied
      rcases leftApplied with ⟨leftInput, leftValues, leftTyped, leftEq⟩
      rcases rightApplied with ⟨rightInput, rightValues, rightTyped, rightEq⟩
      exact leftEq.trans rightEq.symm
    · rw [if_neg color] at leftApplied rightApplied
      exact wf.apply_unique identifier values left right
        leftApplied rightApplied

private theorem colorApp_shape {identifier : Ident}
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

private theorem colorSig_wf : colorSig.WF where
  literalSort := by
    intro literal present
    cases literal <;>
      simp [colorSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  appSorts := by
    intro identifier argumentSorts resultSort inferred
    have present : colorSig.containsIdent identifier = true :=
      colorSig.inferApp_present identifier
        (argumentSorts.map some).toArray (by rw [inferred]; rfl)
    rcases colorApp_shape present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    simp only [Sig.containsSortList_cons, Sig.containsSortList_nil,
      Bool.and_true]
    constructor
    · simp [colorSig, Sig.containsSort, Sig.ofClassifiers,
        colorSortArity?]
    · rw [Sig.containsSort.eq_def]
      simp [intSort, colorSig, Sig.ofClassifiers,
        colorSortArity?, Sig.containsSortList.eq_def]

private theorem boxSig_getApp :
    boxSig.inferApp? boxGet #[some boxSort] =
      some (.ok (some colorSort)) := by
  simp [boxSig, Sig.ofClassifiers, boxContainsIdent,
    inferBoxApp, requireArity, requireSort]
  rfl

private theorem boxApp_shape {identifier : Ident}
    {argumentSorts : List SSort} {resultSort : SSort}
    (present : boxSig.containsIdent identifier = true)
    (inferred : boxSig.inferApp? identifier
      (argumentSorts.map some).toArray = some (.ok (some resultSort))) :
    identifier = boxGet ∧ argumentSorts = [boxSort] ∧
      resultSort = colorSort := by
  have identifierEq : identifier = boxGet := of_decide_eq_true present
  subst identifier
  refine ⟨rfl, ?_⟩
  cases argumentSorts with
  | nil =>
      simp [boxSig, Sig.ofClassifiers, boxContainsIdent,
        inferBoxApp, requireArity] at inferred
      change Except.error _ = Except.ok _ at inferred
      contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          by_cases firstEq : first = boxSort
          · subst first
            simp [boxSig, Sig.ofClassifiers, boxContainsIdent,
              inferBoxApp, requireArity, requireSort,
              Pure.pure, Except.pure] at inferred
            injection inferred with resultEq
            exact ⟨rfl, Option.some.inj resultEq.symm⟩
          · simp [boxSig, Sig.ofClassifiers, boxContainsIdent,
              inferBoxApp, requireArity, requireSort, firstEq] at inferred
            change Except.error _ = Except.ok _ at inferred
            contradiction
      | cons second tail =>
          simp [boxSig, Sig.ofClassifiers, boxContainsIdent,
            inferBoxApp, requireArity] at inferred
          change Except.error _ = Except.ok _ at inferred
          contradiction

private theorem boxSig_wf : boxSig.WF where
  literalSort := by
    intro literal present
    cases literal <;>
      simp [boxSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  appSorts := by
    intro identifier argumentSorts resultSort inferred
    have present : boxSig.containsIdent identifier = true :=
      boxSig.inferApp_present identifier
        (argumentSorts.map some).toArray (by rw [inferred]; rfl)
    rcases boxApp_shape present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    simp [boxSig, boxSort, colorSort, Sig.containsSort,
      Sig.ofClassifiers, boxSortArity?]

/-- Color is an uninterpreted-sort theory with a typed, total `rank`
operation. `Struct.WF` states precisely the usual EUF carrier and function
conditions; no equation constrains which integer rank a color receives. -/
private def colorTheory : Crush.Metatheory.SMT.Theory colorSig where
  sig_wf := colorSig_wf
  Models := Struct.WF
  models_wf := id
  iso_closed := Struct.WF.ofIso

/-- Box contributes the concrete sort `Box Color` and a total projection. Its
laws are ordinary many-sorted EUF laws. -/
private def boxTheory : Crush.Metatheory.SMT.Theory boxSig where
  sig_wf := boxSig_wf
  Models := Struct.WF
  models_wf := id
  iso_closed := Struct.WF.ofIso

private def env : Theory.Env where
  sigEnv := sigEnv
  sig_wf := sigEnv_wf
  decl := fun theory =>
    Fin.cases Int.theory
      (fun rest => Fin.cases colorTheory
        (fun rest => Fin.cases boxTheory
          (fun impossible => nomatch impossible) rest) rest) theory

@[simp] private theorem env_decl_int : env.decl intId = Int.theory := by
  rfl

@[simp] private theorem env_decl_color : env.decl colorId = colorTheory := by
  rfl

@[simp] private theorem env_decl_box : env.decl boxId = boxTheory := by
  rfl

/-- The expanded model has a well-formed reduct for Color. This is the EUF
totality proof for `color.rank`; it is independent of any command assertion. -/
private theorem colorReduct_wf (model : RelModel)
    (integers : Int.Interp (Model.reduct model intSig)) :
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
    rcases colorApp_shape present inferred with
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
        colorSortArity?, intSort], integers.int 0, integers.intTyped 0, ?_, ?_⟩
    · change ∃ value, [input] = [value] ∧
        model.inSort colorSort value ∧ integers.int 0 = integers.int 0
      exact ⟨input, rfl, inputTyped, rfl⟩
    · intro other applied
      change ∃ value, [input] = [value] ∧
        model.inSort colorSort value ∧ other = integers.int 0 at applied
      rcases applied with ⟨otherInput, valuesEq, otherTyped, outputEq⟩
      exact outputEq

/-- A fixed Color value used to realize the concrete `Box Color` projection. -/
private noncomputable def colorDefault (model : RelModel) : model.Value :=
  Classical.choose (model.sortNonempty colorSort)

private theorem colorDefault_typed (model : RelModel) :
    model.inSort colorSort (colorDefault model) :=
  Classical.choose_spec (model.sortNonempty colorSort)

/-- Extend one model by a total `box.get : Box Color → Color` graph. -/
private noncomputable def expandBox (model : RelModel) : RelModel where
  Value := model.Value
  inSort := model.inSort
  sortNonempty := model.sortNonempty
  bool := model.bool
  boolTyped := model.boolTyped
  boolInjective := model.boolInjective
  literal := model.literal
  literalTyped := model.literalTyped
  apply := fun identifier values output =>
    if identifier = boxGet then
      ∃ input, values = [input] ∧ model.inSort boxSort input ∧
        output = colorDefault model
    else
      model.apply identifier values output

private theorem expandBox_wf (model : RelModel) (wf : model.WF) :
    (expandBox model).WF where
  bool_exhaustive := wf.bool_exhaustive
  apply_unique := by
    intro identifier values left right leftApplied rightApplied
    change (if identifier = boxGet then _ else _) at leftApplied rightApplied
    by_cases box : identifier = boxGet
    · rw [if_pos box] at leftApplied rightApplied
      rcases leftApplied with ⟨leftInput, leftValues, leftTyped, leftEq⟩
      rcases rightApplied with ⟨rightInput, rightValues, rightTyped, rightEq⟩
      exact leftEq.trans rightEq.symm
    · rw [if_neg box] at leftApplied rightApplied
      exact wf.apply_unique identifier values left right
        leftApplied rightApplied

private def expandBoxIntegers (model : RelModel)
    (integers : Int.Interp (Model.reduct model intSig)) :
    Int.Interp (Model.reduct (expandBox model) intSig) where
  int := integers.int
  intTyped := integers.intTyped
  intInjective := integers.intInjective
  intExhaustive := integers.intExhaustive
  numeral := integers.numeral
  ge := by
    intro left right output
    change model.Value at output
    have law := integers.ge left right output
    change model.apply (.symb ">=")
        [integers.int left, integers.int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false) at law
    change (expandBox model).apply (.symb ">=")
        [integers.int left, integers.int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false)
    simpa [expandBox, boxGet] using law

private theorem colorValuesTyped_ofExpandBox (model : RelModel) :
    ∀ {sorts values},
      Struct.ValuesTyped (Model.reduct (expandBox model) colorSig)
        sorts values →
      Struct.ValuesTyped (Model.reduct model colorSig) sorts values
  | _, _, .nil => .nil
  | _, _, .cons present head tail =>
      .cons present head (colorValuesTyped_ofExpandBox model tail)

private theorem expandBoxColor_wf (model : RelModel)
    (wf : (Model.reduct model colorSig).WF) :
    (Model.reduct (expandBox model) colorSig).WF where
  sortNonempty := wf.sortNonempty
  boolTyped := wf.boolTyped
  literalSort := wf.literalSort
  literalTyped := wf.literalTyped
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    have identifierEq : identifier = colorRank := of_decide_eq_true present
    have notBox : identifier ≠ boxGet := by
      simp [identifierEq, colorRank, boxGet]
    have oldTyped : Struct.ValuesTyped (Model.reduct model colorSig)
        argumentSorts values := by
      exact colorValuesTyped_ofExpandBox model typed
    rcases wf.appTyped identifier present argumentSorts resultSort inferred
        values oldTyped with
      ⟨resultPresent, output, outputTyped, applied, unique⟩
    refine ⟨resultPresent, output, outputTyped, ?_, ?_⟩
    · change (if identifier = boxGet then _ else
        model.apply identifier values output)
      rw [if_neg notBox]
      exact applied
    · intro other otherApplied
      change (if identifier = boxGet then _ else
        model.apply identifier values other) at otherApplied
      rw [if_neg notBox] at otherApplied
      exact unique other otherApplied

private theorem boxReduct_wf (model : RelModel) :
    (Model.reduct (expandBox model) boxSig).WF where
  sortNonempty := by
    intro sort present
    exact model.sortNonempty sort
  boolTyped := by
    intro present value
    exact model.boolTyped value
  literalSort := by
    intro literal present
    cases literal <;>
      simp [boxSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  literalTyped := by
    intro literal present
    cases literal <;>
      simp [boxSig, Sig.containsLiteral, Sig.ofClassifiers] at present
  appTyped := by
    intro identifier present argumentSorts resultSort inferred values typed
    rcases boxApp_shape present inferred with
      ⟨identifierEq, argumentSortsEq, resultSortEq⟩
    subst identifier
    subst argumentSorts
    subst resultSort
    rcases Struct.ValuesTyped.exists_cons typed with
      ⟨input, tail, rfl, inputTyped, tailTyped⟩
    have tailEq := Struct.ValuesTyped.eq_nil tailTyped
    subst tail
    refine ⟨by
      simp [boxSig, colorSort, Sig.containsSort,
        Sig.ofClassifiers, boxSortArity?],
      colorDefault model, colorDefault_typed model, ?_, ?_⟩
    · change ∃ value, [input] = [value] ∧
        model.inSort boxSort value ∧
          colorDefault model = colorDefault model
      exact ⟨input, rfl, inputTyped, rfl⟩
    · intro other applied
      change ∃ value, [input] = [value] ∧
        model.inSort boxSort value ∧ other = colorDefault model at applied
      rcases applied with ⟨otherInput, valuesEq, otherTyped, outputEq⟩
      exact outputEq

/-- One shared full model satisfies every dependency-closed combination of
Int, Color, and Box. Thus the three-way test cannot pass through an empty
model class. -/
private theorem combModels_exists (comb : Theory.Comb env) :
    ∃ model : RelModel, Theory.Comb.Models comb model := by
  rcases Int.models_exists with ⟨model, witness⟩
  rcases witness with ⟨modelWF, intModels⟩
  rcases intModels.2 with ⟨integers⟩
  let colored := expandColor model integers
  have coloredWF : colored.WF := expandColor_wf model modelWF integers
  have coloredIntegers : Int.Interp (Model.reduct colored intSig) :=
    expandColorIntegers model integers
  let boxed := expandBox colored
  have boxedWF : boxed.WF := expandBox_wf colored coloredWF
  have boxedIntModels : Int.Models (Model.reduct boxed intSig) :=
    Int.models boxed boxedWF (expandBoxIntegers colored coloredIntegers)
  have boxedColorModels : colorTheory.Models
      (Model.reduct boxed colorSig) := by
    unfold colorTheory
    exact expandBoxColor_wf colored (colorReduct_wf model integers)
  have boxedBoxModels : boxTheory.Models (Model.reduct boxed boxSig) := by
    unfold boxTheory
    exact boxReduct_wf colored
  refine ⟨boxed, ⟨boxedWF, ?_⟩⟩
  intro theory active
  cases id_cases theory with
  | inl equal =>
      subst theory
      change Int.theory.Models (Model.reduct boxed intSig)
      unfold Int.theory
      exact boxedIntModels
  | inr rest =>
      cases rest with
      | inl equal =>
          subst theory
          rw [env_decl_color]
          change colorTheory.Models (Model.reduct boxed colorSig)
          exact boxedColorModels
      | inr equal =>
          subst theory
          rw [env_decl_box]
          change boxTheory.Models (Model.reduct boxed boxSig)
          exact boxedBoxModels

private abbrev commands : Array Command := #[
  .assert (.forallE #[("boxed", boxSort)]
    (.symbApp "=" #[
      .app colorRank #[.app boxGet #[.bvar 0]],
      .app colorRank #[.app boxGet #[.bvar 0]]]))]

/-- The same registry drives checking, so every admitted symbol has a semantic
theory entry. The proof is kernel reduction through the total checker. -/
private theorem commands_wellTyped :
    modeledScriptWellTypedWith sigEnv commands = true := by
  prove_modeled_script_well_typed
  rw [sigEnv_eqRawIntApp]
  simp
  rfl

/-- Requirement traversal selects Color through the nested `Box Color` sort
and the rank application. -/
private theorem commands_useColor :
    sigEnv.usesCommands commands colorId = true := by
  decide

/-- Requirement traversal selects Box from its sort constructor and
projection symbol. -/
private theorem commands_useBox :
    sigEnv.usesCommands commands boxId = true := by
  decide

/-- The syntax itself does not mention an integer literal, integer sort, or
integer operator; Int is selected through Color's declared dependency. -/
private theorem commands_doNotUseIntDirectly :
    sigEnv.usesCommands commands intId = false := by
  simp [SigEnv.usesCommands, SigEnv.usesCommand,
    SigEnv.usesSortCtor, SigEnv.selects,
    sigEnv, sortProvider,
    coreSig, Sig.containsSortCtor, Sig.ofClassifiers,
    coreSortArity?, coreContainsIdent, boxSort, colorSort]
  unfold Term.symbApp
  simp [SigEnv.usesIdent, SigEnv.selects, identProvider,
    coreSig, Sig.ofClassifiers, coreContainsIdent]

private theorem commands_activateColor :
    (Theory.Comb.ofCommands env commands).active colorId := by
  exact Theory.Comb.active_of_used commands_useColor

private theorem commands_activateBox :
    (Theory.Comb.ofCommands env commands).active boxId := by
  exact Theory.Comb.active_of_used commands_useBox

private theorem commands_activateInt :
    (Theory.Comb.ofCommands env commands).active intId := by
  apply Theory.DepClosure.dependency
    (Theory.Comb.active_of_used commands_useColor)
  change intId ∈ sigEnv.depIds colorId
  simp [sigEnv, deps, colorId]

/-- Generic dependency closure follows the complete Box → Color → Int
chain even when only Box is selected directly. -/
private theorem singletonBox_activateInt :
    (Theory.Comb.singleton env boxId).active intId := by
  let comb := Theory.Comb.singleton env boxId
  have boxActive : comb.active boxId := by
    apply Theory.Comb.active_of_required
    simp
  have colorActive : comb.active colorId :=
    comb.deps boxId boxActive colorId (by
      change colorId ∈ sigEnv.depIds boxId
      simp [sigEnv, deps, boxId])
  exact comb.deps colorId colorActive intId (by
    change intId ∈ sigEnv.depIds colorId
    simp [sigEnv, deps, colorId])

/-- Every model of the induced combination satisfies the reflexive running
example. The proof composes Box and Color totality before applying logical
equality. -/
private theorem models_satisfyCommands (model : RelModel)
    (models : Theory.Comb.Models (Theory.Comb.ofCommands env commands) model) :
    model.SatisfiesCommands commands := by
  have colorModels : colorTheory.Models (Model.reduct model colorSig) := by
    have selected := models.theory colorId commands_activateColor
    rw [env_decl_color] at selected
    change colorTheory.Models (Model.reduct model colorSig) at selected
    exact selected
  unfold colorTheory at colorModels
  have boxModels : boxTheory.Models (Model.reduct model boxSig) := by
    have selected := models.theory boxId commands_activateBox
    rw [env_decl_box] at selected
    change boxTheory.Models (Model.reduct model boxSig) at selected
    exact selected
  unfold boxTheory at boxModels
  intro command member
  simp at member
  subst command
  apply Eval.forallTrue
  intro values typed
  rcases ValuesTyped.exists_cons typed with
    ⟨input, tail, rfl, inputTyped, tailTyped⟩
  have tailEq := ValuesTyped.eq_nil tailTyped
  subst tail
  have boxTyped : Struct.ValuesTyped (Model.reduct model boxSig)
      [boxSort] [input] :=
    .cons (by
      simp [boxSig, boxSort, colorSort, Sig.containsSort,
        Sig.ofClassifiers, boxSortArity?]) inputTyped .nil
  rcases boxModels.appTyped boxGet (by rfl) [boxSort] colorSort
      boxSig_getApp [input] boxTyped with
    ⟨colorPresent, color, colorTyped, boxApplied, boxUnique⟩
  have boxEval : Eval model [input]
      (.app boxGet #[.bvar 0]) color := by
    apply Eval.symbol (by decide)
    · exact .cons (Eval.bvar rfl) .nil
    · exact boxApplied
  have colorTypedForRank : Struct.ValuesTyped (Model.reduct model colorSig)
      [colorSort] [color] :=
    .cons (by
      simp [colorSig, Sig.containsSort, Sig.ofClassifiers,
        colorSortArity?]) colorTyped .nil
  rcases colorModels.appTyped colorRank (by rfl) [colorSort] intSort
      (by simpa using colorSig_rankApp) [color] colorTypedForRank with
    ⟨resultPresent, output, outputTyped, applied, unique⟩
  have rankEval : Eval model [input]
      (.app colorRank #[.app boxGet #[.bvar 0]]) output := by
    apply Eval.symbol (by decide)
    · exact .cons boxEval .nil
    · exact applied
  exact Eval.eqTrue rankEval rankEval rfl

/-- The exact mixed-theory command has a model of the exact command-induced
combination, not merely separately inhabited component theories. -/
private theorem commands_haveModel :
    ∃ model : RelModel,
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
