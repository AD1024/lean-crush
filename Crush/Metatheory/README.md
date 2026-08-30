# Crush metatheory

## Notation

Import [`Crush.Metatheory.Notation`](Notation.lean) and write
`open scoped Crush.Metatheory` for the shared proof notation. Notation whose
definition would introduce an import cycle is declared beside the corresponding
construction.

| Notation | Meaning | Lean definition |
|---|---|---|
| `⟦e⟧[M, ρ]` | Denotation of `e` in model `M` under valuation `ρ` | [`Notation.lean`](Notation.lean), [`HO/Semantics.lean`](HO/Semantics.lean), [`FO/FamilySemantics.lean`](FO/FamilySemantics.lean) |
| `M ⊨ φ` | Satisfaction of a closed formula | [`Notation.lean`](Notation.lean) |
| `M ⊨ᵀ T` | Satisfaction of every formula in a theory | [`Notation.lean`](Notation.lean) |
| `⌊τ⌋` | First-order erasure of a higher-order type | [`Notation.lean`](Notation.lean), [`FO/Core.lean`](FO/Core.lean) |
| `⌊Γ⌋^⋆` | Pointwise first-order erasure of a context | [`Notation.lean`](Notation.lean) |
| `𝒟⟦e⟧` | Classic unary defunctionalization | [`Notation.lean`](Notation.lean), [`Defunctionalization/Translate.lean`](Defunctionalization/Translate.lean) |
| `𝓕⟦e⟧` | Total flattened translation result | [`Defunctionalization/Flattened/Translate.lean`](Defunctionalization/Flattened/Translate.lean) |
| `𝒶⟦e⟧[E]` | Ordinary raw SMT encoding under `E` | [`SMT/Representation.lean`](SMT/Representation.lean) |
| `𝒢⟦e⟧[G]` | Guard-aware raw SMT encoding under `G` | [`SMT/Guarded.lean`](SMT/Guarded.lean) |
| `vₛ ≈[R, τ] vₜ` | Logical relation between source and target values | [`Notation.lean`](Notation.lean), [`Defunctionalization/LogicalRelation.lean`](Defunctionalization/LogicalRelation.lean) |
| `ρₛ ≈ᵥ[R] ρₜ` | Pointwise logical relation between valuations | [`Notation.lean`](Notation.lean) |
| `FV(e)` | Duplicate-free free-variable positions of `e` | [`Notation.lean`](Notation.lean), [`Defunctionalization/Collect.lean`](Defunctionalization/Collect.lean) |
| `B ⊢ᴰ` | Datatype positions in block `B` | [`Datatype/Core.lean`](Datatype/Core.lean) |
| `B ⊢ᶜ[d] C` | References to constructor `C` of datatype `d` in `B` | [`Datatype/Core.lean`](Datatype/Core.lean) |
| `C ⊢ᶠ F` | References to field `F` of constructor `C` | [`Datatype/Core.lean`](Datatype/Core.lean) |

Proof statements conventionally use `σ` for signatures, `Γ` and `Δ` for
contexts, `τ` for types or sorts, `φ` for formulas, `T` for theories, `M` for
models, `ρ` for source valuations or renamings, and `ν` for target valuations.
Executable state and allocation code uses descriptive names when they convey
more information.

## Main results

The proved endpoint is semantic unsatisfiability of an exact finite intrinsic
higher-order theory sharing one signature. It does not assign a denotation to
arbitrary `Lean.Expr`, and correctness of an external solver remains a separate
boundary.

1. `Flattened.translate_denote` proves preservation of term denotation by the
   total flattened translation; `generated_valid` proves every generated
   closure equation and extensionality formula in the same canonical model.
   See [`Defunctionalization/Flattened/Denotation.lean`](Defunctionalization/Flattened/Denotation.lean)
   and [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean).

2. `Flattened.model_extension_theory` extends one model of a finite source
   theory to the combined flattened target theory, and
   `target_theories_unsat_implies_source_unsat` reflects unsatisfiability back
   to the complete source theory. See
   [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean).

3. `SMT.encode_theories` gives an exact semantic command-set representation of
   the combined flattened theory. `SMT.representation_sound` constructs one raw
   SMT model satisfying native datatype commands, ordinary declarations, and
   assertions; `commands_unsat_implies_source_theory_unsat` is the corresponding
   reflection theorem. See [`SMT/Representation.lean`](SMT/Representation.lean)
   and [`SMT/Soundness.lean`](SMT/Soundness.lean).

4. `Datatype.ctor_inj`, `ctor_ne`, `ctor_cases`, `sel_ctor`, `test_ctor`, and
   the strict-height theorem give productive monomorphic datatype blocks finite
   free-algebra semantics. `SMT.Datatype.EnvRepresentation.native_valid` proves
   the exact dependency-ordered native command prefix. See
   [`Datatype/Semantics.lean`](Datatype/Semantics.lean),
   [`SMT/DatatypeCanonical.lean`](SMT/DatatypeCanonical.lean), and
   [`SMT/DatatypeRepresentation.lean`](SMT/DatatypeRepresentation.lean).

5. `FO.FamilyTerm.guardDenote_rel` preserves terms across a common carrier and
   symbol relation. `SMT.guardTerm_rel_eval` connects that semantics to the
   guard-aware raw syntax, and `SMT.guarded_lift` validates native commands,
   certified derived definitions, ordinary declarations, and guarded assertions
   in one raw model. See [`FO/Guarded.lean`](FO/Guarded.lean) and
   [`SMT/GuardedSoundness.lean`](SMT/GuardedSoundness.lean).

6. `VCG.runTheory_represents` and `runGuardedTheory_represents` prove that fresh
   stateful VCG runs retain the exact aggregate representation.
   `TheoryStateRepresents.unsat_source` and
   `runGuardedTheory_unsat_implies_source_unsat` compose the lowering proof to
   intrinsic source-theory unsatisfiability. See
   [`VCG/Stateful.lean`](VCG/Stateful.lean) and
   [`VCG/Soundness.lean`](VCG/Soundness.lean).

7. `Reification.reifyTheory?` retains an exact ordered fact list reified under
   one datatype environment and ordinary signature bridge. Its witness is
   structural, not a denotational theorem for arbitrary Lean expressions. See
   [`Reification/Witness.lean`](Reification/Witness.lean).

8. `VCG.TheoryAgreement.build?` checks mutual inclusion between a normalized
   production snapshot and the intrinsic guarded command set. Its
   `unsat_source` theorem reflects unsatisfiability of the complete live snapshot
   to the retained intrinsic source theory; `SingleFactAgreement` is the
   singleton specialization. See [`VCG/Production.lean`](VCG/Production.lean).
