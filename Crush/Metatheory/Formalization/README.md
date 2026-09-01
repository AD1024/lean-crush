# Metatheory notation and main results

## Notation

The theorem-facing Lean notation is defined in [`../Notation.lean`](../Notation.lean).
In particular, `M ⊨ φ` denotes semantic satisfaction, while `⊢` is reserved
for syntactic entailment. The mathematical presentation uses `Σ` for signatures,
`Γ` for contexts, `τ` for types or sorts, `e` for terms, `φ` for formulas,
`T` for theories, `M` for models, and `ρ` for valuations.

## Main results

- [`Flattened/ModelExtension.lean`](../Defunctionalization/Flattened/ModelExtension.lean)
  proves semantic preservation of flattened defunctionalization for complete
  finite Higher-order theories.
- [`SMT/GuardedSoundness.lean`](../SMT/GuardedSoundness.lean) proves that the
  guarded First-order-to-SMT encoding preserves satisfaction in a constructed
  model.
- [`VCG/CommandEquivalence.lean`](../VCG/CommandEquivalence.lean) proves that
  unsatisfiability of a well-typed, supported emitted SMT command sequence
  reflects to unsatisfiability of the represented Higher-order source theory.
- [`metatheory.tex`](metatheory.tex) presents the definitions, assumptions,
  examples, proof composition, and exact scope of these results.
