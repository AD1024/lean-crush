# Lowering soundness audit

Audit baseline: `c04208d` (`Certify inductive datatype lowering metatheory`).

## Verdict

The intrinsic lowering theorem is sound and well factored:

```text
intrinsic HO sentence
  -> total flattened FO theory
  -> exact raw SMT command representation
  -> semantic unsatisfiability reflection
```

The proof includes the translated sentence itself, validates every generated
closure/equation formula, uses one induced raw model for declarations and
assertions, and gives native datatypes finite free-algebra semantics. There are
no `sorry`, `admit`, or declared proof axioms in this path.

The live production pipeline is not yet covered by that theorem. Production
retains exact certificates for selected datatype and guard commands, but it does
not construct a whole-array representation of the surrounding extensible
translation. This is the principal remaining soundness boundary.

## Boundary matrix

| Boundary | Main evidence | Audit result |
|---|---|---|
| `Lean.Expr` to intrinsic HO | `Reification.reifySentence?`, `ReificationWitness` | Executably type-checked and shape-checked, but intentionally has no denotation theorem for arbitrary `Lean.Expr`. |
| Intrinsic HO to flattened FO | `translate_denote`, `generated_valid`, `model_extension` | Complete semantic preservation for the intrinsic language. |
| Flattened FO to ordinary SMT | `TheoryRepresentation`, `representation_sound` | Exact syntax plus one-model semantic lifting. |
| Native datatype commands | `Datatype.command_sound`, `EnvRepresentation.native_valid` | Correct for source models satisfying `Datatype.Env.Lawful`; rank excludes cyclic values. |
| Guarded/enlarged carriers | `guardTerm_rel_eval`, `guarded_lift` | Correct relative to an explicit carrier relation, guard semantics, derived graph, and native-command validity. |
| Stateful intrinsic VCG | `run_represents`, `runGuarded_represents` | Exact, but `run`/`runGuarded` build fresh pure states rather than refining a completed production run. |
| Live production commands | `CertifiedDataEnv`, `ProductionAgreement`, command-index traces | Exact reflection interface now exists, but the live allocator does not yet construct its representation witnesses. |
| Solver result | `CommandsUnsatisfiable` | Semantic premise only. External solver and proof-replay correctness remain separate. |

## Soundness findings

### P0: production whole-run agreement is missing

`VCG.run` installs `VCG.commands` in a fresh `TranslateState`. It does not call
the extensible production `emitTerm` procedure. The latter is deliberately
marked with `TrustReason.direct`.

`CertifiedDataEnv` improves the production boundary substantially: every
native datatype and recursive guard command is linked to an exact position in
the final command snapshot, and it now retains `ReifiedSentenceFor` indexed by
that exact datatype environment, signature tail, and bridge whenever the whole
fact reifies. `ProductionAgreement` links that sentence to the complete final
snapshot and proves reflection from `certificate.emitted`; top-level `:named`
attributes are removed only through a proved semantic-equivalence theorem.

However, the following witnesses remain caller premises rather than products
of the production run:

- `CertifiedDataEnv.Represents`;
- `CertifiedDataEnv.GuardRepresentation`;
- `ProductionAgreement`, including the complete
  `GuardedTheoryRepresentation` after annotation normalization.

Consequently, the reflection theorem for `CertifiedDataEnv.emitted` exists, but
live production cannot yet construct its `ProductionAgreement` automatically.

Required completion criterion:

1. build the shared `SMT.Encoding`, datatype representation, guard
   representation, and declaration trace from the final allocator state;
2. construct `ProductionAgreement`, including command order and every
   surrounding assertion/declaration;
3. expose semantic reflection only from a `TranslateState` carrying that
   completed witness.

### Repaired: guarded reflection no longer restricts the quantified model class

The lower-level `runGuarded_unsat_under` accurately concludes
`UnsatisfiableUnder` a sigma contract containing `GuardModel`. In the audited
baseline this was the only guarded corollary, so failure to construct a
`GuardModel` silently removed a datatype-lawful source model from the
quantification.

The follow-up repair separates the layers:

- `UnaryGuards` records only a fresh unary graph; absence of a unary identifier
  no longer incorrectly asserts that the whole semantic guard is total. This is
  essential when built-in integer `>=` guards a sort omitted by the unary graph.
- `GuardAllocation` records identifier injectivity, freshness, and exact trace
  matching once, independently of any model.
- `GuardModel.ofIntView` derives graph uniqueness, graph freshness, and composed
  term semantics for the standard integer-plus-datatype combination.
- `GuardInterpretation` realizes that static allocation for every lawful source
  model. `runGuarded_unsat_implies_source_unsat` therefore concludes ordinary
  `Datatype.Env.Unsatisfiable`; its quantified model class contains no target
  construction evidence.

The remaining production task is to construct `GuardAllocation` and a uniform
`GuardInterpretation` from the final live allocator evidence. This is now an
explicit encoding-level premise, rather than a hidden restriction on source
models, and belongs to the whole-run agreement work above.

### P1: the Lean boundary is structural, not semantic

Successful reification calls `checked?` at every accepted node and returns an
intrinsically typed term. Its witness records recursive source/target shape
agreement. This is useful refinement evidence, but it is not a kernel theorem
relating evaluation of `Lean.Expr` to `Term.denote`.

The former `encoded_unsat_implies_source_unsat` theorem accepted this witness as
an unused premise while concluding only intrinsic-source unsatisfiability. It
has been removed because it did not establish an additional semantic result.
Future documentation and theorem names should say "intrinsic VCG soundness"
unless a genuine Lean-expression semantics is added.

### P1: solver correctness is intentionally outside this proof

Every final reflection theorem assumes `CommandsUnsatisfiable`, defined as the
absence of a semantic raw model. A solver's `unsat` response is not itself a
proof of this proposition. Checked Alethe replay is the operational trust path,
but it is not composed into these model-theoretic theorems.

### P2: the native datatype proof has three legitimate layers

`DatatypeCanonical`, `DatatypeLifted`, and `DatatypeCarry` look repetitive, but
they currently prove different facts:

- validity in the ordinary canonical model;
- validity immediately after enlarging one block carrier;
- preservation through later dependency blocks.

Deleting any layer today would remove a used theorem. The best future
simplification is a general raw-model isomorphism/transport theorem. With that
abstraction, much of the law-by-law transport in `DatatypeCarry` should become
derivable once, rather than reproving constructor, selector, tester,
exhaustiveness, and rank properties separately.

## Consolidation completed in this audit

- Guarded and unguarded FO syntax now use one guard-parameterized recursive
  encoder; the duplicate encoder and its recursive equivalence proof were
  removed.
- `Bool`, `Int`, `String`, and bit-vector SMT sorts now have one definition in
  `Crush.SMT.Syntax`; `(smtSort| ...)` is the common nullary-sort syntax.
- Repeated `ValuesTyped` inversion proofs are shared by all datatype model
  layers.
- Repeated duplicate-free map/finite-range proofs are shared by the datatype
  core.
- Equality-wrapper representation predicates that carried no information were
  removed.
- The empty `TypeCorrespondence` record and unused datatype-occurrence trace
  were removed from reification witnesses.
- `DataBridge.core` was renamed to `DataBridge.toModelEnv`; `core` did not say
  which of the several environments it produced.
- The guarded reflection theorem was renamed `runGuarded_unsat_under` so its
  restricted model class is visible at the call site.
- `𝒢⟦e⟧[G]` now parallels the ordinary `𝒶⟦e⟧[E]` notation, and theorem-facing
  notation follows the `σ`, `Γ`, `τ`, `e`, `φ`, `T`, `M`, `ρ` convention.
- Production certificates retain an exact environment-indexed
  `ReifiedSentenceFor`; `ProductionAgreement` is isolated in
  `VCG/Production.lean` and accounts explicitly for semantically transparent
  root assertion annotations.

## Naming and organization rules

- Use `σ`, `Γ`, `τ`, `e`, `φ`, `T`, `M`, and `ρ` in compact mathematical
  notation and theorem statements; use descriptive English in executable
  state/allocation code.
- Reserve `Encoding` for the shared FO-to-SMT encoding. A future broad rename
  should change `SMT.Datatype.Encoding` to `BlockEncoding`; until that change is
  made, use `dataEncoding` rather than the ambiguous local name `data`.
- Use `...Representation` for exact syntax/provenance and `...Semantics` or
  `...Lawful` for model obligations. Do not call an equality wrapper a
  representation.
- Use `(smt| ...)` and `(smtSort| ...)` for literal SMT syntax. Use constructors
  directly only for dynamic indexed identifiers, dynamic binder arrays, or
  dynamic argument arrays that the quotations cannot express.
- Keep the pure intrinsic VCG under `VCG/`. Keep production-refinement theorems
  in a separate `VCG/Production.lean` module so a fresh specification run cannot
  be confused with agreement for the live translator.

## Ordered follow-up goal

1. Construct production `SMT.Encoding` and block/guard representations from
   final allocator evidence.
2. Construct whole-array `ProductionAgreement` during the live run; the exact
   intrinsic sentence and reflection theorem are now retained.
3. Construct production `GuardAllocation` and `GuardInterpretation` from final
   allocator evidence; the semantic constructors and unrestricted reflection
   theorem are now available.
4. Store the completed agreement/interpretation in a proved production state
   and select it before the unrestricted direct fallback.
5. Only then attempt the raw-model transport abstraction that can shrink
   `DatatypeCarry`.
