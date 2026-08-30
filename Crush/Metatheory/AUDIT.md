# Lowering soundness audit

Audit baseline: `c04208d` (`Certify inductive datatype lowering metatheory`).

## Verdict

The intrinsic lowering theorem is sound and well factored:

```text
finite intrinsic HO theory
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
| Intrinsic HO to flattened FO | `translate_denote`, `generated_valid`, `model_extension_theory` | Complete semantic preservation for each sentence and for a finite theory sharing one signature. |
| Flattened FO to ordinary SMT | `TheoryRepresentation`, `representation_sound` | Exact syntax plus one-model semantic lifting. |
| Native datatype commands | `Datatype.command_sound`, `EnvRepresentation.native_valid` | Correct for source models satisfying `Datatype.Env.Lawful`; rank excludes cyclic values. |
| Guarded/enlarged carriers | `guardTerm_rel_eval`, `guarded_lift` | Correct relative to an explicit carrier relation, guard semantics, derived graph, and native-command validity. |
| Stateful intrinsic VCG | `runTheory_represents`, `runGuardedTheory_represents` | Exact for finite theories, but these functions build fresh pure states rather than refining a completed production run. |
| Live production commands | `CertifiedDataEnv`, `TheoryAgreement`, command-index traces | Exact whole-theory reflection and a proof-producing array check exist; `buildScript` does not yet retain the required common reification or construct allocator representation witnesses. |
| Solver result | `CommandsUnsatisfiable` | Semantic premise only. External solver and proof-replay correctness remain separate. |

## Soundness findings

### P0: production cannot yet construct whole-run agreement

`VCG.run` installs `VCG.commands` in a fresh `TranslateState`. It does not call
the extensible production `emitTerm` procedure. The latter is deliberately
marked with `TrustReason.direct`.

`CertifiedDataEnv` improves the production boundary substantially: every
native datatype and recursive guard command is linked to an exact position in
the final command snapshot, and it now retains `ReifiedSentenceFor` indexed by
that exact datatype environment, signature tail, and bridge whenever the whole
fact reifies. `SingleFactAgreement` links that sentence to a complete final
single-fact snapshot and proves reflection from `certificate.emitted`;
top-level `:named` attributes and the leading `set-logic` command are removed
only through proved semantic-equivalence theorems.

The audit now supplies the missing aggregate specification and semantic proof:

- `reifyDataSignatureMany`, `ReifiedSentencesFor`, and `reifyTheory?` select one
  environment and retain exact pointwise witnesses without reordering facts;
- `translatedTheories` and `model_extension_theory` flatten the complete source
  theory and extend one source model across every generated target obligation;
- `encodeTheories`, `theoryCommands`, and their guarded/stateful counterparts
  retain an exact combined target representation;
- `commands_unsat_implies_source_theory_unsat` and
  `Representation.theory_unsat` prove unguarded and guarded reflection;
- `TheoryAgreement.build?` checks the normalized completed production array
  against that exact aggregate encoding. `SingleFactAgreement` now delegates to
  the singleton instance instead of maintaining a second proof path.

The following witnesses still remain caller premises rather than products of
the production run:

- `CertifiedDataEnv.Representation`;
- `CertifiedDataEnv.GuardRepresentation`;
- the shared encoding and datatype/guard representation premises needed by
  `TheoryAgreement.build?`;
- a retained invocation of common-signature reification for the exact fact
  array consumed by `buildScript`.

Consequently, the reflection theorem for `CertifiedDataEnv.emitted` exists, but
live production cannot yet supply all inputs to its executable agreement check.
Once those static representation witnesses exist, `TheoryAgreement.build?`
compares the complete normalized production snapshot with the exact intrinsic
encoding and returns proof-carrying agreement only when structural equality
succeeds.

`SingleFactAgreement` remains only as a compatibility specialization for a
script containing exactly the certificate's retained fact. `buildScript`
normally combines hypotheses, selected premises, generated instances, and the
negated goal, so its sound conclusion must use `TheoryAgreement` and the
complete common-signature theory.

Required completion criterion:

1. retain `reifyTheory?`/`ReifiedSentencesFor` for the exact complete production
   fact array rather than constructing independent fact-local signatures;
2. build the shared `SMT.Encoding`, datatype representation, guard
   representation, and declaration trace from the final allocator state;
3. run `TheoryAgreement.build?`, whose structural comparison checks command
   order and every surrounding assertion/declaration;
4. expose semantic reflection only from a `TranslateState` carrying that
   completed witness.

The key construction mismatch is now explicit. `SMT.Encoding` is a total,
globally injective assignment for every intrinsic `FOSort` and flattened
`Symbol`; the production allocator records only the finite Lean-keyed names
encountered in one run. The finite trace cannot justify the total fields by
itself, and filling unobserved cases with arbitrary defaults would invalidate
injectivity. Completion therefore needs either (a) one proved total intrinsic
allocator whose finite restriction drives command emission, or (b) a redesign
of the raw-model theorem around a finite supported symbol/sort environment. The
current evidence should not be coerced into a global `SMT.Encoding` by an
unchecked cast.

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
- `GuardRepresentation` records identifier injectivity, freshness, exact trace
  matching, and command syntax once, independently of any model.
- `GuardModel.ofIntView` derives graph uniqueness, graph freshness, and composed
  term semantics for the standard integer-plus-datatype combination.
- `GuardInterpretation` realizes that static allocation for every lawful source
  model. `runGuarded_unsat_implies_source_unsat` therefore concludes ordinary
  `Datatype.Env.Unsatisfiable`; its quantified model class contains no target
  construction evidence.

The remaining production task is to construct `GuardRepresentation` and a uniform
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
- Production refinement is isolated in `VCG/Production.lean`.
  `TheoryAgreement` consumes exact common-environment `ReifiedSentencesFor` and
  accounts explicitly for semantically transparent root assertion annotations;
  `SingleFactAgreement` is its retained-fact singleton specialization.
- The proof records formerly named `CertifiedDataTrace.Represents` and
  `CertifiedDataEnv.Represents` are now `...Representation`, matching
  `TheoryRepresentation`, `GuardRepresentation`, and their exact-syntax role.
- The unused parallel `VCG.TranslationStatus` hierarchy was removed. The pure
  route now returns one `TranslateState`; `StateRepresents` carries semantic
  evidence, while `TranslateState.status` remains the operational trust marker.
- The unused intrinsic `certifiedPrimitive` symbol and the never-populated
  generated `guards`/`primitiveConstraints` channels were removed. Live hook
  certificates remain in `Hooks.lean`; carrying semantic functions inside the
  globally name-injective structural symbol family was both unnecessary and an
  obstacle to constructing a concrete encoding.
- The native block-local datatype `Encoding` was renamed `BlockEncoding`, and
  production projections now say `blockEncoding`; `SMT.Encoding` consequently
  refers only to the shared FO-to-SMT representation.
- Finite theories now have one semantic and executable route from exact ordered
  common-environment reification through combined flattening and SMT encoding.
  The former one-fact production proof is a singleton specialization of
  `TheoryAgreement`, not a duplicated reflection argument.
- Higher-order theory append/satisfiability helpers introduced during this work
  but unused by the proof were removed; only the source-theory satisfaction and
  unsatisfiability notions consumed by reflection remain.

## Naming and organization rules

- Use `σ`, `Γ`, `τ`, `e`, `φ`, `T`, `M`, and `ρ` in compact mathematical
  notation and theorem statements; use descriptive English in executable
  state/allocation code.
- Reserve `Encoding` for the shared FO-to-SMT encoding. The block-local native
  datatype encoder is `SMT.Datatype.BlockEncoding`; use `dataEncoding` rather
  than the ambiguous local name `data` when both occur together.
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

1. Redesign `SMT.Encoding` around finite support, or introduce a proved total
   intrinsic allocator whose finite restriction drives production emission.
2. Construct production `SMT.Encoding` and block/guard representations from
   final allocator evidence.
3. Retain the already-defined common-signature `ReifiedSentencesFor` and run
   `TheoryAgreement.build?` for the exact fact array consumed by `buildScript`.
4. Construct production `GuardRepresentation` and `GuardInterpretation` from final
   allocator evidence; the semantic constructors and unrestricted reflection
   theorem are now available.
5. Store the completed agreement/interpretation in a proved production state
   and select it before the unrestricted direct fallback.
6. Only then attempt the raw-model transport abstraction that can shrink
   `DatatypeCarry`.
