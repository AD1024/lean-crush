# Crush defunctionalization metatheory

This directory is the proof-facing model of Crush's higher-order translation.
The live translator still consumes Lean `Expr`; the metatheory deliberately
separates semantic correctness from that reification/refinement boundary.

## Mathematical notation

Import `Crush.Metatheory.Notation` and write `open scoped Crush.Metatheory` to
enable the proof-facing notation. Inline comments beside each declaration in
`Notation.lean` give its precise meaning. The main forms are
`⟦e⟧[M, ρ]` for denotation, `M ⊨ φ` and `M ⊨ᵀ T` for satisfaction,
`𝒟⟦e⟧` for core defunctionalization, `⌊τ⌋` and `⌊Γ⌋^⋆` for erasure,
`vₛ ≈[R, τ] vₜ` and `ρₛ ≈ᵥ[R] ρₜ` for the logical relations, and `FV(e)`
for free-variable positions.

## Worklist status

1. **Intrinsically typed HO and FO languages — complete.** See `HO/Core.lean`,
   `FO/Core.lean`, and `FO/Family.lean`.
2. **Model semantics — complete.** See `HO/Semantics.lean`, `FO/Semantics.lean`, and
   `FO/FamilySemantics.lean`.
3. **Total collection and classic defunctionalization — complete.** See
   `Defunctionalization/Collect.lean`, `Annotate.lean`, and `Core.lean`.
4. **Source/target logical relation — complete for the classic verified core.**
   See `Defunctionalization/LogicalRelation.lean`.
5. **Fundamental lemma — complete for every modeled source constructor.** See
   `Defunctionalization/Fundamental.lean`.
6. **Model extension and target-unsat implies source-unsat — complete.** Exact
   capture reconstruction, closure validity, and the final contrapositive
   are in `Defunctionalization/ModelExtension.lean`.
7. **Flattened application and partial-application eta — complete at the typed
   semantic layer.** `EtaCorrectness.lean` proves eta normalization preserves
   denotation. `FlattenedApplication.lean` gives the production n-ary symbol a
   canonical semantics and proves one-symbol application-spine preservation.
8. **Guarded subtype encodings — complete for the generic contract, `Nat ↪ Int`,
   and optional guarded fields.** See `Guarded/Encoding.lean`. The live
   `wfCondition` and `guardSort` paths use named syntax constructors matching the
   proved guard shapes.
9. **Route the live translator through the verified pass — complete for the
   modeled fragment, with explicit fallback outside it.**
   `Bridge/Type.lean` reifies normalized nondependent arrows, proves their
   flattened telescope and `FO.appDecl`, and production `arrowShape?` and
   `declareArrowSort` now retain and consume that witness. `Bridge/Capture.lean`
   proves exact occurrence membership and uniqueness for the total production
   capture collector used by `emitClosure`, and defines the exact typed
   `ClosureCaptureCertificate`. `Bridge/Term.lean` and `Bridge/Reify.lean` now
   implement typed signature/context lookup, typed smart constructors for every
   modeled term former, executable reification of the modeled Lean fragment, and
   proof-producing closure certification. Production closure declarations route
   capture types through these same `TypeBridge` values. `emitClosure` now invokes
   `certifyLocalClosure?` and consumes its proof-backed context for the
   modeled fragment, including finite signatures of nondependent uninterpreted
   constants; unsupported closures take an explicit fallback. Full
   `ProductionClosure.lean` proves the actual arbitrary-arity closure equation:
   the exact-capture constructor followed by production's single flattened
   `app` denotes the fully applied source lambda. `Bridge/Command.lean` makes live
   app declarations, closure declarations, and guarded defining assertions
   proof-carrying; `TranslateState` retains those command certificates plus the
   dependent semantic closure proof referenced by each verified equation.
   `emitCertifiedCommand` atomically emits the command stored in its certificate,
   ruling out stateful command/certificate drift.
   Production structural-symbol allocation now maintains a proof-carrying trace
   with duplicate-free emitted names; `key_eq_of_name_eq` proves allocation
   injectivity, and live tests cover fresh allocation and same-key reuse.
   `LiveCertifiedConstant` now ties a live `Expr` to the exact de Bruijn constant
   returned by its finite `SignatureBridge`, carries the constant-indexed
   canonical semantic certificate, and is retained with the emitted production
   symbol by `defaultApp`; live tests check that symbol against the injective
   allocation trace. Every app declaration, closure declaration, and closure
   equation now derives its principal structural dependencies from its own
   `CommandCertificate`; `emitCertifiedStructuralCommand` snapshots the allocation
   trace and retains a proof that each dependency belongs to it. The restricted
   certified handler path described below runs before trusted lowerings.
10. **Certified built-in and user-extension hooks — complete for restricted
    flattened primitive mappings.**
    `Hooks.lean` defines the arbitrary-arity `TermHookCertificate` preservation
    contract and reuses guarded `Encoding` as `SortHookCertificate`. It also
    defines `CanonicalTermHookCertificate`, which quantifies over every source
    model and fixes Crush's actual canonical model-extension relation; this
    prevents vacuous certification by choosing an always-true relation. Live
    registry entries carry `HandlerTrust`; all existing unrestricted attributes
    are explicitly `.trustedBoundary`, never implicitly certified.
    `CanonicalConstantHookCertificate` further indexes the contract by the exact
    intrinsic constant, and `flattenedDenote_canonical_related` proves the
    production flattened interpretation satisfies it at every modeled type.
    The live reifier constructs and retains this certificate for supported
    `defaultApp` declarations. `PrimitiveHookCertificate` separates the proved
    canonical preservation theorem from the explicit `LeanDeclarationDenotes`
    and `SolverSymbolDenotes` assumptions. The proof-erased
    `CertifiedPrimitiveMapping` constructor preserves those declaration/symbol
    indices at runtime; `@[crush_certified_lower]` registers only that restricted
    mapping, derives its handler mechanically, checks flattened arity, and records
    successful dispatch. Boolean `Not` dogfoods the path, and `Test.Extension`
    constructs and executes a user-defined certified primitive. Arbitrary
    metaprogram handlers remain explicitly trusted rather than certified.

## Current trusted/refinement boundary

The proofs do not assume that arbitrary live `Expr` translation is correct.
They prove the typed core transformations and expose the following obligations
for the executable bridge:

- reify supported nondependent Lean types and terms into the intrinsic source
  language;
- extend the current verified arrow witness through emitted SMT sort translation;
- show those emitted finite declarations reify `ProductionSymbol`;
- extend the restricted certified DSL when additional handler shapes are needed;
  arbitrary metaprogram handlers intentionally remain trusted extensions;
- connect production well-formedness discovery for recursive datatypes to a
  recursively constructed guarded `Encoding`.

All theorems in this directory are free of proof placeholders.
