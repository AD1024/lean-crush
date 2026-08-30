import Crush.Metatheory.Defunctionalization.LogicalRelation

/-!
# Metatheory notation

This file centralizes the mathematical notation shared by the higher-order source
language, first-order target language, and defunctionalization proofs. The notation is
scoped: import this module and use `open scoped Crush.Metatheory` to enable it.
The later `𝓕⟦e⟧` notation is declared beside the total translator because its
definition cannot be imported here without introducing an import cycle.

Mathematical binders follow one convention throughout theorem-facing notation:
`σ` for signatures, `Γ` for contexts, `τ` for types/sorts, `e` for terms, `φ`
for formulas, `T` for theories, `M` for models, and `ρ` for valuations. Longer
English names remain preferable in executable code where the role is operational
rather than mathematical.

The object-language symbol `⊢` is intentionally not declared here. It is reserved
for syntactic entailment in a proof calculus; intrinsic terms and datatype references
are represented by their indexed Lean types instead.
-/

namespace Crush.Metatheory.Defunctionalization

/-- The value relation selected by a bundled source/target model relation. -/
abbrev ModelRelation.ValueRelated {signature : Signature}
    {source : Model signature} {target : FO.FamilyModel (CoreSymbol signature)}
    (models : ModelRelation source target) (ty : Ty)
    (sourceValue : ty.Denote source.Base)
    (targetValue : (FO.FOSort.ofTy ty).Denote target.carriers) : Prop :=
  ValueRel source target models.baseRel ty sourceValue targetValue

/-- The pointwise valuation relation selected by a bundled model relation. -/
abbrev ModelRelation.ValuationsRelated {signature : Signature}
    {source : Model signature} {target : FO.FamilyModel (CoreSymbol signature)}
    (models : ModelRelation source target) {context : Context}
    (sourceValuation : Valuation source.Base context)
    (targetValuation : FO.FamilyValuation target (targetContext context)) : Prop :=
  ValuationRel source target models.baseRel sourceValuation targetValuation

end Crush.Metatheory.Defunctionalization

namespace Crush.Metatheory

-- Projection notation is intentionally polymorphic across HO, FO, and family terms.
set_option quotPrecheck false

/-- `⟦e⟧[M, ρ]` is the value denoted by `e` in model `M` under valuation `ρ`. -/
scoped notation:max "⟦" e "⟧[" M ", " ρ "]" => (e).denote M ρ

/-- `M ⊨ φ` says that the closed formula `φ` is true in model `M`. -/
scoped notation:50 M:51 " ⊨ " φ:51 => (M).Satisfies φ

/-- `M ⊨ᵀ T` says that `M` satisfies every formula in theory `T`. -/
scoped notation:50 M:51 " ⊨ᵀ " T:51 => (M).SatisfiesTheory T

/-- `⌊τ⌋` is the first-order sort obtained by erasing higher-order type `τ`. -/
scoped notation:max "⌊" τ "⌋" => FO.FOSort.ofTy τ

/-- `𝒟⟦e⟧` is the first-order syntax produced by core defunctionalization of `e`.
Unlike semantic brackets, these brackets denote a syntax-to-syntax translation. -/
scoped notation:max "𝒟⟦" e "⟧" => Defunctionalization.defunctionalizeCore e

/-- `⌊Γ⌋^⋆` is the pointwise first-order erasure of source context `Γ`.
The star distinguishes context erasure from the single-type erasure `⌊τ⌋`. -/
scoped notation:max "⌊" Γ "⌋^⋆" => Defunctionalization.targetContext Γ

/-- `vₛ ≈[R, τ] vₜ` says that the source and target values are logically related
at source type `τ` by source/target model relation `R`. -/
scoped notation:50 sourceValue:51 " ≈[" models ", " ty "] " targetValue:51 =>
  Defunctionalization.ModelRelation.ValueRelated models ty sourceValue targetValue

/-- `ρₛ ≈ᵥ[R] ρₜ` says that corresponding entries of the source and target
valuations are logically related by `R`. -/
scoped notation:50 sourceValuation:51 " ≈ᵥ[" models "] " targetValuation:51 =>
  Defunctionalization.ModelRelation.ValuationsRelated models sourceValuation targetValuation

/-- `FV(e)` is the duplicate-free, left-to-right list of free de Bruijn positions
occurring in `e`. -/
scoped notation:max "FV(" e ")" => Defunctionalization.freeVarIndices e

end Crush.Metatheory
