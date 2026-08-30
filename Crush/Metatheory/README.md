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
| `𝒶⟦e⟧[E]` | Ordinary untyped SMT encoding under `E` | [`SMT/Representation.lean`](SMT/Representation.lean) |
| `𝒢⟦e⟧[G]` | Guard-aware untyped SMT encoding under `G` | [`SMT/Guarded.lean`](SMT/Guarded.lean) |
| `vₛ ≈[R, τ] vₜ` | Logical relation between source and target values | [`Notation.lean`](Notation.lean), [`Defunctionalization/LogicalRelation.lean`](Defunctionalization/LogicalRelation.lean) |
| `ρₛ ≈ᵥ[R] ρₜ` | Pointwise logical relation between valuations | [`Notation.lean`](Notation.lean) |
| `FV(e)` | Duplicate-free free-variable positions of `e` | [`Notation.lean`](Notation.lean), [`Defunctionalization/Collect.lean`](Defunctionalization/Collect.lean) |

The symbol `⊢` is reserved for syntactic entailment in an explicitly specified
proof calculus. Intrinsic typing and datatype references use the indexed types
`Term`, `FamilyTerm`, `DataRef`, `CtorRef`, and `FieldRef` directly.

Proof statements conventionally use `Σ` for signatures, `Γ` and `Δ` for
contexts, `τ` for types or sorts, `φ` for formulas, `T` for theories, `M` for
models, `r` for typed renamings, `ρ` for source valuations, and `ν` for target
valuations.
Executable state and allocation code uses descriptive names when they convey
more information.

## Main results

The proved endpoint is semantic unsatisfiability of an exact finite intrinsic
higher-order theory sharing one signature. It does not assign a denotation to
arbitrary `Lean.Expr`, and correctness of an external solver remains a separate
boundary.

1. `Flattened.translate_denote` proves preservation of term denotation by the
   total flattened translation; `generatedFormulas_valid` proves every generated
   closure equation and extensionality formula in the same canonical model.
   See [`Defunctionalization/Flattened/Denotation.lean`](Defunctionalization/Flattened/Denotation.lean)
   and [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean).

2. `Flattened.model_extension_theory` extends one model of a finite source
   theory to the combined flattened target theory, and
   `target_theories_unsat_implies_source_unsat` reflects unsatisfiability back
   to the complete source theory. See
   [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean).

3. `SMT.encode_theories` proves that the generated command array and the
   combined flattened theory have exactly the same satisfying SMT models.
   `SMT.representation_sound` constructs one untyped
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
   guard-aware untyped syntax, and `SMT.guarded_lift` validates native commands,
   recursively defined guards, ordinary declarations, and guarded assertions
   in one untyped SMT model. See [`FO/Guarded.lean`](FO/Guarded.lean) and
   [`SMT/GuardedSoundness.lean`](SMT/GuardedSoundness.lean).

6. `VCG.theoryCommands_represents` and
   `guardedTheoryCommands_represents` prove that finite-theory command
   generation has the expected unguarded and guarded meanings.
   `theoryCommands_unsat_implies_source_unsat` composes the unguarded lowering
   proof to intrinsic source-theory unsatisfiability. See
   [`VCG/Generate.lean`](VCG/Generate.lean).

7. `Reification.reifyTheory?` retains an exact ordered fact list reified under
   one datatype environment and ordinary signature bridge. Its witness is
   structural, not a denotational theorem for arbitrary Lean expressions. See
   [`Reification/Witness.lean`](Reification/Witness.lean).

8. `VCG.ProductionTheoryAgreement.build?` checks that the final production
   command array and the intrinsic guarded command array contain the same
   semantically relevant commands. Its `unsat_source` theorem reflects
   unsatisfiability of the final production commands to the complete retained
   intrinsic source theory; `ProductionFactAgreement` is the single-fact
   specialization. See [`VCG/Production.lean`](VCG/Production.lean).
