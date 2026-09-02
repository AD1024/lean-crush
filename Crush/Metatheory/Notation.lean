import Crush.Metatheory.Defunctionalization.Collect
import Crush.Metatheory.HO.Semantics
import Crush.Metatheory.FO.FamilySemantics

/-!
# Metatheory notation

This file centralizes the mathematical notation shared by the higher-order source
language, first-order target language, and defunctionalization proofs. The notation is
scoped: import this module and use `open scoped Crush.Metatheory` to enable it.
The later `𝓕⟦e⟧` notation is declared beside the total translator because its
definition cannot be imported here without introducing an import cycle.

Mathematical binders follow one convention throughout theorem-facing notation.
LaTeX uses `Σ` for signatures; Lean uses the descriptive name `signature`
because `Σ` is dependent-pair syntax. Lean uses `Γ` for contexts, `τ` for
types/sorts, `e` for terms, `φ` for formulas, `T` for theories, `M` for models,
and `ρ` for valuations. Longer
English names remain preferable in executable code where the role is operational
rather than mathematical.

The object-language symbol `⊢` is intentionally not declared here. It is reserved
for syntactic entailment in a proof calculus; typed terms and datatype references
are represented by their indexed Lean types instead.
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
