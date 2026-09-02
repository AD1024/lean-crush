import Crush.Metatheory

open scoped Crush.Metatheory

/-!
Focused compile-time checks for the standalone HO-to-FO metatheory.
-/

namespace Crush.Metatheory.Defunctionalization.Tests

private def entity : Ty := .base ⟨"Entity"⟩

private abbrev signature : Signature :=
  [.arrow entity (.arrow entity entity), entity]

private def binary : Const signature (.arrow entity (.arrow entity entity)) :=
  .here

private def value : Const signature entity := .there .here

/-- The source language contains genuine higher-order values and application. -/
private def partialApplication :
    ClosedTerm signature (.arrow entity entity) :=
  .app (.const binary) (.const value)

/- A residual function value is represented by a generated closure equation. -/
#eval show IO Unit from do
  unless 𝓕⟦partialApplication⟧.equations.length == 1 do
    throw <| IO.userError "partial application did not generate one closure equation"

/-- Translation preserves denotation in the canonical first-order model. -/
example (model : Model signature) :
    ⟦𝓕⟦partialApplication⟧.term⟧[
        canonicalModel model, targetVal model (Valuation.empty model.Base)] =
      toCanonical model (.arrow entity entity)
        ⟦partialApplication⟧[model, Valuation.empty model.Base] :=
  translate_denote model partialApplication (Valuation.empty model.Base)

private def reflexiveFormula : Sentence signature :=
  .eq (.app (.const binary) (.const value))
    (.app (.const binary) (.const value))

/-- Every generated equation and the translated source sentence share one
canonical first-order model whenever the source sentence is satisfied. -/
example (model : Model signature) (sourceValid : model ⊨ reflexiveFormula) :
    canonicalModel model ⊨ᵀ translatedTheory reflexiveFormula :=
  model_extension model reflexiveFormula sourceValid

/-- FO unsatisfiability of the complete generated theory reflects to HO
unsatisfiability. -/
example
    (targetUnsat : FO.FamilyTheoryUnsatisfiable
      (translatedTheory reflexiveFormula)) :
    Unsatisfiable reflexiveFormula :=
  target_unsat_implies_source_unsat reflexiveFormula targetUnsat

/-- The reflection theorem also composes over a finite source theory. -/
example
    (targetUnsat : FO.FamilyTheoryUnsatisfiable
      (translatedTheories [reflexiveFormula])) :
    TheoryUnsatisfiable [reflexiveFormula] :=
  target_theories_unsat_implies_source_unsat [reflexiveFormula] targetUnsat

end Crush.Metatheory.Defunctionalization.Tests
