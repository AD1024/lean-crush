import Crush.Metatheory.Defunctionalization.Collect
import Crush.Metatheory.HO.Semantics
import Crush.Metatheory.FO.FamilySemantics

/-!
# Metatheory notation

Enable the shared mathematical notation with `open scoped Crush.Metatheory`.
The translator defines `𝓕⟦e⟧` separately to avoid an import cycle.
Theorem-facing binders use `signature`, `Γ`, `τ`, `e`, `φ`, `T`, `M`, and `ρ` for
signatures, contexts, types, terms, formulas, theories, models, and valuations.
Lean reserves `Σ` for dependent pairs; `⊢` remains reserved for proof-calculus entailment
rather than the indexed types representing syntax.
-/

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

/-- `⌊Γ⌋^⋆` is the pointwise first-order erasure of source context `Γ`.
The star distinguishes context erasure from the single-type erasure `⌊τ⌋`. -/
scoped notation:max "⌊" Γ "⌋^⋆" => Defunctionalization.targetContext Γ

/-- `FV(e)` is the duplicate-free, left-to-right list of free de Bruijn positions
occurring in `e`. -/
scoped notation:max "FV(" e ")" => Defunctionalization.freeVarIndices e

end Crush.Metatheory
