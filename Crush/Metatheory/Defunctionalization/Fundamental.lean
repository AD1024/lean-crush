import Crush.Metatheory.Notation

/-!
# Fundamental lemma for unary reference defunctionalization
-/

namespace Crush.Metatheory.Defunctionalization

open scoped Crush.Metatheory

variable {signature : Signature}
variable {source : Model signature}
variable {target : FO.FamilyModel (CoreSymbol signature)}

/-- Evaluation of a source term and its total core translation produces related
values under related valuations. -/
theorem fundamental (models : ModelRelation source target) :
    {Γ : Context} → {τ : Ty} →
    (e : Term signature Γ τ) →
    (ρ : Valuation source.Base Γ) →
    (ν : FO.FamilyValuation target (targetContext Γ)) →
    ρ ≈ᵥ[models] ν →
    ⟦e⟧[source, ρ] ≈[models, τ] ⟦𝒟⟦e⟧⟧[target, ν] := by
  intro Γ τ e
  induction e with
  | var ref =>
      intro ρ ν hρν
      simpa [Term.denote, FO.FamilyTerm.denote.eq_1, defunctionalizeCore] using
        hρν ref
  | const constant =>
      intro ρ ν _
      simp only [Term.denote, defunctionalizeCore]
      rw [FO.FamilyTerm.denote.eq_2, FO.FamilyArgs.apply.eq_1]
      exact models.constRelated constant
  | boolLit value =>
      intro _ _ _
      cases value <;>
        simp [Term.denote, FO.FamilyTerm.denote.eq_3,
          FO.FamilyTerm.denote.eq_4, defunctionalizeCore]
  | not body bodyIH =>
      intro ρ ν hρν
      simp only [Term.denote, defunctionalizeCore]
      rw [FO.FamilyTerm.denote.eq_5]
      exact not_congr (bodyIH ρ ν hρν)
  | and left right leftIH rightIH =>
      intro ρ ν hρν
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_6,
          defunctionalizeCore] using
        and_congr
        (leftIH ρ ν hρν)
        (rightIH ρ ν hρν)
  | or left right leftIH rightIH =>
      intro ρ ν hρν
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_7,
          defunctionalizeCore] using
        or_congr
        (leftIH ρ ν hρν)
        (rightIH ρ ν hρν)
  | imp left right leftIH rightIH =>
      intro ρ ν hρν
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_8,
          defunctionalizeCore] using
        imp_congr
        (leftIH ρ ν hρν)
        (rightIH ρ ν hρν)
  | iff left right leftIH rightIH =>
      intro ρ ν hρν
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_9,
          defunctionalizeCore] using
        iff_congr
        (leftIH ρ ν hρν)
        (rightIH ρ ν hρν)
  | eq left right leftIH rightIH =>
      intro ρ ν hρν
      simpa [ValueRel, Term.denote, FO.FamilyTerm.denote.eq_10,
          defunctionalizeCore] using
        models.equalityIff _ _ _ _ _
        (leftIH ρ ν hρν)
        (rightIH ρ ν hρν)
  | lam body bodyIH =>
      intro ρ ν hρν
      simpa [Term.denote, defunctionalizeCore] using
        models.closureRelated body ρ ν hρν
  | app fn argument fnIH argumentIH =>
      intro ρ ν hρν
      simpa [Term.denote, FO.FamilyTerm.denote.eq_2,
          FO.FamilyArgs.apply.eq_1, FO.FamilyArgs.apply.eq_2,
          defunctionalizeCore] using
        fnIH ρ ν hρν
        ⟦argument⟧[source, ρ]
        ⟦𝒟⟦argument⟧⟧[target, ν]
        (argumentIH ρ ν hρν)
  | forallE body bodyIH =>
      intro ρ ν hρν
      simp only [Term.denote, defunctionalizeCore,
        FO.FamilyTerm.denote.eq_11]
      constructor
      · intro sourceForall targetValue
        obtain ⟨sourceValue, valueRelated⟩ := models.rightTotal _ targetValue
        exact (bodyIH
          (ρ.extend sourceValue)
          (ν.extend targetValue)
          (hρν.extend valueRelated)).mp (sourceForall sourceValue)
      · intro targetForall sourceValue
        obtain ⟨targetValue, valueRelated⟩ := models.leftTotal _ sourceValue
        exact (bodyIH
          (ρ.extend sourceValue)
          (ν.extend targetValue)
          (hρν.extend valueRelated)).mpr (targetForall targetValue)
  | existsE body bodyIH =>
      intro ρ ν hρν
      simp only [Term.denote, defunctionalizeCore,
        FO.FamilyTerm.denote.eq_12]
      constructor
      · rintro ⟨sourceValue, sourceBody⟩
        obtain ⟨targetValue, valueRelated⟩ := models.leftTotal _ sourceValue
        exact ⟨targetValue, (bodyIH
          (ρ.extend sourceValue)
          (ν.extend targetValue)
          (hρν.extend valueRelated)).mp sourceBody⟩
      · rintro ⟨targetValue, targetBody⟩
        obtain ⟨sourceValue, valueRelated⟩ := models.rightTotal _ targetValue
        exact ⟨sourceValue, (bodyIH
          (ρ.extend sourceValue)
          (ν.extend targetValue)
          (hρν.extend valueRelated)).mpr targetBody⟩

/-- Empty source and target valuations are related vacuously. -/
theorem emptyValuationsRelated (models : ModelRelation source target) :
    Valuation.empty source.Base ≈ᵥ[models] FO.Valuation.empty target.carriers := by
  intro ty ref
  cases ref

/-- Closed formulas and their translated target formulas have equivalent truth
in related models. -/
theorem fundamental_sentence (models : ModelRelation source target)
    (φ : Sentence signature) :
    source ⊨ φ ↔ target ⊨ 𝒟⟦φ⟧ := by
  simpa [Model.Satisfies, FO.FamilyModel.Satisfies] using
    fundamental models φ
      (Valuation.empty source.Base)
      (FO.Valuation.empty target.carriers)
      (emptyValuationsRelated models)

end Crush.Metatheory.Defunctionalization
