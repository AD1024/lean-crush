import Crush.Metatheory.Notation

/-!
# Fundamental lemma for classic defunctionalization
-/

namespace Crush.Metatheory.Defunctionalization

open scoped Crush.Metatheory

variable {signature : Signature}
variable {source : Model signature}
variable {target : FO.FamilyModel (CoreSymbol signature)}

/-- Evaluation of a source term and its total core translation produces related
values under related valuations. -/
theorem fundamental (models : ModelRelation source target) :
    {context : Context} → {ty : Ty} →
    (term : Term signature context ty) →
    (sourceValuation : Valuation source.Base context) →
    (targetValuation : FO.FamilyValuation target (targetContext context)) →
    sourceValuation ≈ᵥ[models] targetValuation →
    ⟦term⟧[source, sourceValuation] ≈[models, ty]
      ⟦𝒟⟦term⟧⟧[target, targetValuation] := by
  intro context ty term
  induction term with
  | var ref =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [Term.denote, FO.FamilyTerm.denote.eq_1, defunctionalizeCore] using
        valuationsRelated ref
  | const constant =>
      intro sourceValuation targetValuation _
      simp only [Term.denote, defunctionalizeCore]
      rw [FO.FamilyTerm.denote.eq_2, FO.FamilyArgs.apply.eq_1]
      exact models.constRelated constant
  | boolLit value =>
      intro _ _ _
      cases value <;>
        simp [Term.denote, FO.FamilyTerm.denote.eq_3,
          FO.FamilyTerm.denote.eq_4, defunctionalizeCore]
  | not body bodyIH =>
      intro sourceValuation targetValuation valuationsRelated
      simp only [Term.denote, defunctionalizeCore]
      rw [FO.FamilyTerm.denote.eq_5]
      exact not_congr (bodyIH sourceValuation targetValuation valuationsRelated)
  | and left right leftIH rightIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_6,
          defunctionalizeCore] using
        and_congr
        (leftIH sourceValuation targetValuation valuationsRelated)
        (rightIH sourceValuation targetValuation valuationsRelated)
  | or left right leftIH rightIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_7,
          defunctionalizeCore] using
        or_congr
        (leftIH sourceValuation targetValuation valuationsRelated)
        (rightIH sourceValuation targetValuation valuationsRelated)
  | imp left right leftIH rightIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_8,
          defunctionalizeCore] using
        imp_congr
        (leftIH sourceValuation targetValuation valuationsRelated)
        (rightIH sourceValuation targetValuation valuationsRelated)
  | iff left right leftIH rightIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_9,
          defunctionalizeCore] using
        iff_congr
        (leftIH sourceValuation targetValuation valuationsRelated)
        (rightIH sourceValuation targetValuation valuationsRelated)
  | eq left right leftIH rightIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_10,
          defunctionalizeCore] using
        models.equalityIff _ _ _ _ _
        (leftIH sourceValuation targetValuation valuationsRelated)
        (rightIH sourceValuation targetValuation valuationsRelated)
  | lam body bodyIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [Term.denote, defunctionalizeCore] using
        models.closureRelated body sourceValuation targetValuation valuationsRelated
  | app fn argument fnIH argumentIH =>
      intro sourceValuation targetValuation valuationsRelated
      simpa [Term.denote, FO.FamilyTerm.denote.eq_2,
          FO.FamilyArgs.apply.eq_1, FO.FamilyArgs.apply.eq_2,
          defunctionalizeCore] using
        fnIH sourceValuation targetValuation valuationsRelated
        (Term.denote source argument sourceValuation)
        (FO.FamilyTerm.denote target (defunctionalizeCore argument) targetValuation)
        (argumentIH sourceValuation targetValuation valuationsRelated)
  | forallE body bodyIH =>
      intro sourceValuation targetValuation valuationsRelated
      simp only [Term.denote, defunctionalizeCore,
        FO.FamilyTerm.denote.eq_11]
      constructor
      · intro sourceForall targetValue
        obtain ⟨sourceValue, valueRelated⟩ := models.rightTotal _ targetValue
        exact (bodyIH
          (sourceValuation.extend sourceValue)
          (targetValuation.extend targetValue)
          (valuationsRelated.extend valueRelated)).mp (sourceForall sourceValue)
      · intro targetForall sourceValue
        obtain ⟨targetValue, valueRelated⟩ := models.leftTotal _ sourceValue
        exact (bodyIH
          (sourceValuation.extend sourceValue)
          (targetValuation.extend targetValue)
          (valuationsRelated.extend valueRelated)).mpr (targetForall targetValue)
  | existsE body bodyIH =>
      intro sourceValuation targetValuation valuationsRelated
      simp only [Term.denote, defunctionalizeCore,
        FO.FamilyTerm.denote.eq_12]
      constructor
      · rintro ⟨sourceValue, sourceBody⟩
        obtain ⟨targetValue, valueRelated⟩ := models.leftTotal _ sourceValue
        exact ⟨targetValue, (bodyIH
          (sourceValuation.extend sourceValue)
          (targetValuation.extend targetValue)
          (valuationsRelated.extend valueRelated)).mp sourceBody⟩
      · rintro ⟨targetValue, targetBody⟩
        obtain ⟨sourceValue, valueRelated⟩ := models.rightTotal _ targetValue
        exact ⟨sourceValue, (bodyIH
          (sourceValuation.extend sourceValue)
          (targetValuation.extend targetValue)
          (valuationsRelated.extend valueRelated)).mpr targetBody⟩

/-- Empty source and target valuations are related vacuously. -/
theorem emptyValuationsRelated (models : ModelRelation source target) :
    Valuation.empty source.Base ≈ᵥ[models] FO.Valuation.empty target.carriers := by
  intro ty ref
  cases ref

/-- Closed formulas and their translated target formulas have equivalent truth
in related models. -/
theorem fundamental_sentence (models : ModelRelation source target)
    (formula : Sentence signature) :
    source ⊨ formula ↔ target ⊨ 𝒟⟦formula⟧ := by
  simpa [Model.Satisfies, FO.FamilyModel.Satisfies] using
    fundamental models formula
      (Valuation.empty source.Base)
      (FO.Valuation.empty target.carriers)
      (emptyValuationsRelated models)

end Crush.Metatheory.Defunctionalization
