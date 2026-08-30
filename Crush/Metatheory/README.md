# Crush defunctionalization metatheory

This directory formalizes the supported path from Lean syntax to concrete SMT
commands while keeping each semantic boundary explicit:

```text
Lean.Expr
  -- structural reification --> HO.Term
  -- total defunctionalization --> FO family theory
  -- represented encoding --> SMT commands
```

The final conclusion is unsatisfiability of the reified HO sentence. There is no
claimed denotation for arbitrary `Lean.Expr`, and solver correctness remains a
separate concern.

## Active worklist

The dependency-ordered plan for certifying monomorphized user-defined inductive
datatypes is in
[`INDUCTIVE_DATATYPE_PLAN.md`](INDUCTIVE_DATATYPE_PLAN.md). It covers intrinsic
datatype descriptions and free-algebra semantics, Lean declaration reification,
native SMT `declare-datatypes` representation, model lifting, production
agreement, guarded fields, and end-to-end tests.

## Main results

The flattened intrinsic translation is total and proof-producing:

- `Defunctionalization/TranslationResult.lean` retains the translated term,
  declarations, closure equations, guards, extensionality formulas, and
  primitive constraints in source order.
- `Defunctionalization/Flattened/Translate.lean` defines total `translate`.
- `Flattened/Currying.lean` proves `flatApp_eq_unarySpine`,
  `completeApp_denote`, and `etaClosure_eq_partialSpine`.
- `Flattened/Denotation.lean` proves `translate_denote` and
  `flattened_refines_unary` in `canonicalModel`.
- `Flattened/Theory.lean` proves simultaneous `generated_valid`,
  `model_extension`, and `target_unsat_implies_source_unsat`.

The concrete representation layer is deliberately relational; the existing raw
SMT DSL is not made intrinsically typed:

- `HO/Semantics.lean` defines ordinary `Satisfiable`/`Unsatisfiable` and the
  generic proof-relevant `SatisfiableUnder`/`UnsatisfiableUnder`. Datatype and
  interpreted-carrier semantics instantiate the latter with their model
  contracts instead of defining a second kind of HO model.
- `SMT/Semantics.lean` defines the required raw-term and command semantics,
  including semantic `CommandsUnsatisfiable`.
- `SMT/Representation.lean` defines `SortRepresentation`,
  `SymbolRepresentation`, `TermRepresentation`, `TheoryRepresentation`, and the
  pure encoder. Term construction uses `(smt| ...)` wherever its syntax supports
  the required dynamic expression.
- `SMT/Model.lean` constructs the one induced raw model used by every encoded
  component. `ExtraGraph` adds derived native symbols only when their graph is
  disjoint from every encoded source identifier; `ModelExtension.lean` proves
  source typing and raw evaluation are preserved. `SMT/Soundness.lean` proves
  the low-level composition lemmas `lift` and `lift_with_extra`, the complete
  `representation_sound`, and
  `commands_unsat_implies_source_unsat`.

The datatype extension now has a proved native-command core:

- `Datatype/Semantics.lean` defines finite free values and proves `ctor_inj`,
  `ctor_ne`, `ctor_cases`, `sel_ctor`, `test_ctor`, and strict height decrease
  for recursive fields.
- `Datatype/Guarded.lean` lifts any pointwise guarded base representation through
  an arbitrary productive recursive or mutual block. Its single structural
  `Val.WF` predicate replaces the former `Option`-specific lifting and proves
  both guarded encoding/decoding round trips. `Val.wf_iff_selWF` proves that
  this structural predicate is exactly the production-shaped conjunction of
  tester implications over matching selectors.
- Raw `define-funs-rec` commands now have a non-vacuous simultaneous graph
  semantics (`FunDef.Holds` and `FunsRecHold`). Production's datatype guard body
  uses `.bvar 0`, so the raw evaluator reads its local argument directly while
  the SMT-LIB printer continues to render the allocated binder name.
- `SMT/DatatypeGuard.lean` proves `eval_andAll`, `eval_wfClause`, and
  `eval_wfBody` for the exact shared syntax. `SMT/DatatypeGuarded.lean` then
  connects every field clause to its typed guard and proves the exact mutual
  `define-funs-rec` command in `wfDefs_valid`.
- `FO/Guarded.lean` defines one guard-restricted denotation and proves
  `FamilyTerm.guardDenote_lift`: variables, symbols, connectives, equality, and
  both quantifiers in a lifted carrier model denote exactly the encoded source
  term. The more general `FamilyTerm.guardDenote_rel` accepts one uniform
  `ModelRel`, allowing native constructors to keep their free-algebra target
  interpretation while satisfying the same per-symbol preservation contract.
  `Datatype/Carrier.lean` constructs that enlarged carrier and proves the
  constructor, selector, and tester obligations. Selectors preserve the source
  model's unspecified value on nonmatching guarded inputs while still obeying
  the native selector equation on every matching target constructor.
  `Datatype/FamilyModel.lean` installs those operations through one typed
  ownership map and proves `FamilyLawful.extend_rel` for every symbol;
  `Datatype/Flattened.lean` derives its source laws for Crush's actual flattened
  symbol family.
  `SMT/GuardedSoundness.lean` proves `guardTerm_eval` for the exact raw syntax
  and combines the layers in `guardTerm_rel_eval`. `guarded_lift` then validates
  one complete array containing native commands, exact certified derived
  definitions, ordinary declarations, and guarded assertions. Its only
  component premise is `Guarding.Semantics`; `UnaryGuards.semantics` discharges
  that premise uniformly for fresh unary predicates such as datatype `wf_T`.
- `Reification/Datatype.lean` reifies productive ground Lean inductive blocks,
  preserves declaration order, collects dependencies, and rejects indexed,
  higher-order-field, nonproductive, and unsafe indirect-recursive cases.
  Datatype recursors and quotient primitives are also rejected before they can
  be mistaken for ordinary uninterpreted constants; their fallback reasons are
  retained in production state.
  `crush.datatype.certify` opts production into this acceptance check, exact
  constructor/selector ownership, and a retained certificate for the native
  datatype command. It is off by default; the option certifies the datatype
  component rather than the surrounding extensible translation.
- `VCG/Datatype.lean` packages each opt-in production `declare-datatypes`
  command with its exact reified block, allocated encoding, and `CommandWF`
  proof. Production emits and records that command atomically. `CertifiedDataEnv`
  then retains one intrinsically indexed `CertifiedDataTrace`: block identity and
  command count follow from its type, and every dependency-ordered native command
  is proved equal to the command at its recorded production index. After all
  facts are emitted, these traces are rebuilt against the exact final
  `TranslateState.commands`, so no intermediate command prefix is exposed. The
  `CertifiedDataEnv.Represents` boundary records one shared-encoding
  `Representation` for every typed trace entry and assembles those witnesses
  into the single `EnvRepresentation` used by model lifting; it is not a second
  encoder. `CertifiedGuardTrace` performs the same exact final-state indexing
  for recursive `wf_T` commands. `GuardModel` bundles the interpreted prior,
  derived graph, and guard semantics for one source model; `Represents.sound`
  and `Represents.unsat_under` are the combined model and reflection theorems.
- Production discovery first builds one read-only `DatatypePlan` containing the
  complete mutual member, constructor, and ground-field structure. Only after
  discovery finishes does `declareDatatype` allocate names and emit commands,
  preventing mutable allocator state from changing the declaration traversal.
- Guard definitions enter the same `CommandEncoding` and global allocation-link
  arrays as app declarations and closure equations. `DataGuardEncoding` retains
  the exact mutual `FunDef` array and production command; no datatype-specific
  command-trace mechanism was added.
- `SMT/Datatype.lean` emits the exact monomorphic `declare-datatypes` command.
  Its pure `wfBody` builder is also the single implementation of the compact
  tester/selector guard syntax used by production, including omission of empty
  clauses and singleton conjunctions.
- `SMT/DatatypeCanonical.lean` proves native datatype laws in the ordinary
  shared raw model; it does not introduce a second datatype-only value universe.
  `ctor_laws`, `ctor_disjoint`, `exhaustive`, `test_disjoint`, and `rank_lt`
  discharge the native datatype laws; `data_hold` combines them, and
  `command_sound` proves that the canonical model satisfies the emitted command.
  `supported` derives raw syntactic support from block well-formedness,
  productivity, injective allocated names, and no-duplicate raw symbols.
- `SMT/DatatypeLifted.lean` proves the same native command directly at one
  dependency-extension step. `SMT/DatatypeCarry.lean` transports all of those
  laws through later disjoint blocks; `command_sound_carry` is the one-step
  theorem and `EnvRepresentation.lifted_valid` validates the complete native
  prefix in the final folded target. `datatypeCommand_with_extra` then preserves
  that prefix under fresh derived graphs. `block_valid_with_guards` validates one
  native declaration and its exact `wf_T` command together,
  `block_valid_with_int` installs the integer graph used by `Nat`, and
  `EnvRepresentation.sound_with` is the identity-base whole-theory theorem.
  `Lifted.ofBase`, `EnvRepresentation.liftedFrom_valid`, and
  `EnvRepresentation.soundFrom` provide the same result over interpreted base
  carriers such as `Nat → Int`.
- `SMT.Datatype.EnvRepresentation.native_valid` proves the exact ordered native
  command prefix valid for every lawful datatype environment. This is a local
  component certificate, not a second soundness path: `SMT.representation_sound`
  consumes it together with ordinary sort declarations, ordinary symbol
  declarations, and assertions in the same induced model. The empty environment
  is the ordinary no-datatype case.

The live boundary is split by role:

- `Reification/` recognizes the supported nondependent Lean fragment and returns
  intrinsically typed terms with exact signature, context, constructor, and
  capture witnesses. Reification is partial because unsupported Lean syntax is
  outside the modeled fragment.
- `VCG/Generate.lean` composes total HO-to-FO translation with FO-to-SMT encoding.
  `guardedCommands_represents` is the exact guarded counterpart, with the
  certified derived-command segment stated explicitly.
- `VCG/Stateful.lean` defines total `VCG.run`; `run_represents` proves that its
  exact `TranslateState.commands` represents the complete intrinsic theory.
  `runGuarded`, `runGuarded_represents`, and `runGuarded_dataTrace` give the
  guarded route a fresh proved state and exact native command positions.
- `VCG/Soundness.lean` proves `encoded_unsat_implies_source_unsat` and the direct
  executable specialization `run_unsat_implies_source_unsat`. Each theorem takes
  one `EnvRepresentation` indexed by the same `DataBridge` that owns the reified
  source constants; no unrelated datatype environment or datatype-only theorem
  variant can be supplied. An empty bridge covers ordinary encodings, while a
  nonempty representation certifies the native datatype prefix.
  `runGuarded_unsat` reflects the guarded run under the combined datatype and
  interpreted-carrier contract represented by `UnsatisfiableUnder`.

The earlier unary encoding remains under the core defunctionalization modules as
an independent semantic reference, with its logical-relation and model-extension
proofs intact.

## Core correctness theorems

The main correctness argument is the following composition. Names below are
shown relative to `Crush.Metatheory`.

1. **Flattened term preservation**

   `Defunctionalization.Flattened.translate_denote` in
   [`Defunctionalization/Flattened/Denotation.lean`](Defunctionalization/Flattened/Denotation.lean)
   proves that a translated FO term and its HO source have the same denotation
   in the canonical model, after the source value is embedded in its target
   representation.

2. **Validity of generated obligations**

   `Defunctionalization.Flattened.generated_valid` in
   [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean)
   proves that every closure equation, guard, extensionality formula, and
   primitive constraint generated by `translate` holds in the canonical target
   model.

3. **Source-model extension**

   `Defunctionalization.Flattened.model_extension` in
   [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean)
   combines term preservation and generated validity: every model satisfying a
   closed HO formula extends to a model satisfying its complete translated FO
   theory.

4. **Defunctionalization unsatisfiability reflection**

   `Defunctionalization.Flattened.target_unsat_implies_source_unsat` in
   [`Defunctionalization/Flattened/Theory.lean`](Defunctionalization/Flattened/Theory.lean)
   proves that unsatisfiability of the complete translated FO theory implies
   unsatisfiability of the source HO sentence.

5. **Exact FO-to-SMT representation**

   `VCG.commands_represents` in
   [`VCG/Generate.lean`](VCG/Generate.lean) proves that the concrete commands
   returned by the pure VCG encoder are exactly a `TheoryRepresentation` of the
   complete translated FO theory. The underlying encoder theorem is
   `SMT.encode_translation` in
   [`SMT/Representation.lean`](SMT/Representation.lean). For enlarged carriers,
   `VCG.guardedCommands_represents` records the same theory with exact derived
   commands and guard-aware quantifier syntax.

6. **Semantic soundness of SMT representation**

   `SMT.representation_sound` in
   [`SMT/Soundness.lean`](SMT/Soundness.lean) is the single complete model-lifting
   theorem. Given a lawful source model, an exact datatype environment
   representation, and validity of the represented FO theory in the canonical
   target model, it constructs one raw model satisfying every emitted component:
   native datatype commands, ordinary sort declarations, ordinary symbol
   declarations, and assertions. Its corollary
   `SMT.commands_unsat_implies_source_unsat` composes this construction with
   `model_extension` and reflects semantic command unsatisfiability directly to
   datatype-environment-aware source unsatisfiability. The guarded counterpart
   is `SMT.guarded_lift`; `VCG.CertifiedDataEnv.Represents.sound` supplies its
   native and recursive-guard premises from one datatype certificate.

7. **Exact stateful execution**

   `VCG.run_represents` in
   [`VCG/Stateful.lean`](VCG/Stateful.lean) proves that the exact command array in
   the fresh `TranslateState` returned by `VCG.run` represents the complete
   translated theory, including command order. `VCG.runGuarded_represents` and
   `VCG.runGuarded_dataTrace` establish the guarded array and every native
   datatype position in the same way.

8. **Composed intrinsic VCG soundness**

   `VCG.StateRepresents.unsat_source` and
   `VCG.run_unsat_implies_source_unsat` in
   [`VCG/Soundness.lean`](VCG/Soundness.lean) compose the preceding results:

   ```text
   semantic unsatisfiability of VCG.run's exact SMT commands
       ⇒ no lawful source model can extend to the represented FO theory
       ⇒ unsatisfiability of the intrinsic HO source sentence
   ```

   The datatype environment is an ordinary parameter of this result. With
   `env = []`, `Datatype.Env.unsatisfiable_nil_iff` recovers the original source
   proposition. For interpreted base carriers, `VCG.runGuarded_unsat` concludes
   `UnsatisfiableUnder` the combined datatype and `GuardModel` contract, making
   the strengthened model class explicit rather than introducing another HO
   model type.

9. **Structural Lean boundary**

   `VCG.encoded_unsat_implies_source_unsat` in
   [`VCG/Soundness.lean`](VCG/Soundness.lean) additionally accepts a
   `Reification.Reifies` witness for a `Lean.Expr`. Its conclusion deliberately
   remains unsatisfiability of the reified HO sentence: the witness establishes
   typed structural correspondence, not a denotational semantics for arbitrary
   Lean expressions.

The principal supporting application and closure results are
`Defunctionalization.Flattened.TypedArguments.flatApp_eq_unarySpine`,
`Defunctionalization.Flattened.TargetArguments.completeApp_denote`, and
`Defunctionalization.Flattened.etaClosure_eq_partialSpine` in
[`Defunctionalization/Flattened/Currying.lean`](Defunctionalization/Flattened/Currying.lean).

Here `Crush.SMT.CommandsUnsatisfiable` is a semantic proposition about the
command sequence. These theorems do not assert that an external solver's
reported `unsat` verdict is correct. They also apply to the total intrinsic
`VCG.run` route, not automatically to the legacy direct `emitTerm` procedure
described below.

## Proved and trusted execution

`VCG.TranslationStatus` makes the boundary structural:

- `proved` retains the intrinsic source, exact commands, and
  `TheoryRepresentation` theorem;
- `trusted` retains commands and nonempty `TrustReason`s but exposes no semantic
  representation theorem.

The legacy production `emitTerm : Lean.Expr → TranslateM SMT.Term` is always
marked `TrustReason.direct` at its root. Local certified closures and primitives
still retain useful typed evidence, but they do not promote that combined,
extensible direct route to a whole-run proof. Unrestricted term/sort handlers,
lowerings, result lowerings, uncertified closures/constants, and native-HO mode
record additional trust reasons.

After successful `Reification.reifySentence?`, `VCG.run` is the non-partial
defunctionalization and command-generation route. It starts with fresh translation
bookkeeping and therefore cannot inherit commands or trust markers from a legacy
run.

## Notation

Import `Crush.Metatheory.Notation` and write
`open scoped Crush.Metatheory` to enable the shared mathematical notation:

| Notation | Meaning |
|---|---|
| `⟦e⟧[M, ρ]` | denotation of `e` in model `M` under valuation `ρ` |
| `M ⊨ φ` | model satisfaction of a closed formula |
| `M ⊨ᵀ T` | model satisfaction of every formula in a theory |
| `⌊τ⌋` | first-order erasure of a higher-order type |
| `⌊Γ⌋^⋆` | pointwise first-order erasure of a context |
| `𝒟⟦e⟧` | classic unary defunctionalization |
| `𝓕⟦e⟧` | total flattened translation result; declared by `Flattened/Translate.lean` |
| `vₛ ≈[R, τ] vₜ` | source and target values related at type `τ` |
| `ρₛ ≈ᵥ[R] ρₜ` | pointwise related source and target valuations |
| `FV(e)` | duplicate-free free-variable positions of `e` |
| `B ⊢ᴰ` | datatype positions in block `B` |
| `B ⊢ᶜ[d] C` | references to constructor `C` of datatype `d` in `B` |
| `C ⊢ᶠ F` | references to field `F` of constructor `C` |

The flattened development also uses named type shorthands where notation would
hide too much structure:

| Shorthand | Expanded type |
|---|---|
| `TargetTerm σ Γ τ` | a family FO term over flattened symbols in `⌊Γ⌋^⋆`, of sort `⌊τ⌋` |
| `TargetFormula σ Γ` | a Boolean flattened target term in `⌊Γ⌋^⋆` |
| `TargetSentence σ` | a closed flattened target formula |
| `TargetTheory σ` | a list of flattened target sentences |
| `TargetValuation M Γ` | a valuation of `⌊Γ⌋^⋆` in `canonicalModel M` |

Proof-oriented code follows the usual binder convention: `σ` for a signature,
`Γ` and `Δ` for contexts, `τ` for a type, `φ` for a formula, `M` for a model,
`ρ` for a source valuation or renaming, and `ν` for a target valuation. Longer
descriptive names remain preferable in executable translation code and whenever
two objects of the same mathematical role must be distinguished.
