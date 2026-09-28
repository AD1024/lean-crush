# CPC replay implementation plan

The replay engine shares term decoding, checked proof construction, and scope
management across certificate formats. Parsers retain each format's rule names;
inference handlers are indexed by both format and rule. SMT term decoders remain
shared because custom lowerings have the same meaning in either certificate.

## Steps

- [x] Extract the common replay infrastructure and add
  `register_replay_rule Alethe << ... >>` and
  `register_replay_rule CPC << ... >>`, including format-specific attributes.
  Preserve the existing Alethe registration spelling as a compatibility alias.
- [x] Parse cvc5 CPC certificates with explicit conclusions, including shared
  terms, bound variables, assumptions, and scoped subproofs. Unsupported forms
  must decline without accepting unproved assumptions.
- [x] Add CPC handlers through the public registry, reusing checked arithmetic,
  logical, and theory proof helpers. Keep dispatch isolated by format.
- [x] Add `crush.reconstruct "cpc"` (also accept `"CPC"`), configure cvc5's proof
  output, and select the matching parser and handlers. Alethe and CPC both use
  core-guided fallback by default; `crush.reconstruct.fallback false` requires
  certificate replay and skips early closure for reliable replay testing.
- [x] Add parser, registry, scope, soundness, fallback, and live cvc5 tests.
  Reuse existing Alethe obligations for both formats and check proof axioms.
- [x] Update the README and executable Verso manual; build the library, full
  test suite, and manual, then review the final diff.

## Validation boundaries

Every accepted inference and final proof remains checked by Lean. Replay uses
only selected source facts and premises in scope, and restores state on failure.
Proof rules and certificate conclusions are untrusted inputs. Missing rules,
unsupported terms, malformed certificates, and solver serialization errors may
trigger checked core reconstruction, never an implicit trusted discharge.

The default `auto` mode continues to request Alethe, preserving its solver query
and search behavior. CPC is opt-in. No search bounds are increased.

CPC rule coverage is partial. The solver is configured to print explicit
conclusions without parameterized proof macros; the parser also accepts nullary
term sharing. Internal total division and remainder currently require a concrete,
nonzero divisor. Quantifier skolem decoding handles index zero and requires Lean
evidence of nonemptiness. Unsupported forms decline to the configured fallback.

## Completed milestones

1. Shared replay engine and format-indexed registration. Registry isolation,
   priorities, compatibility aliases, Alethe parsing, and term tests pass.
2. CPC parser and inference handlers. Parser tests cover sharing, quantifiers,
   scope boundaries, reused identifiers, and malformed input. Soundness tests
   reject invented assumptions, escaped local assumptions, forged conclusions,
   and handler proofs of the wrong proposition.
3. Tactic integration and regression coverage. Live cvc5 tests re-prove 52 Alethe
   obligations using CPC with fallback disabled and reject any trust, sorry, or
   native-decision axiom. Both formats pass checked fallback tests; strict replay
   still reports errors under `reconstructOrTrust`. Benchmark scripts explicitly
   disable fallback in the existing strict Alethe lane.
4. Documentation and validation. The README, architecture notes, and executable
   manual describe both formats and the default fallback policy. The manual
   builds without warnings and renders the new configuration and extension pages.

## Validation results

Validated with Lean 4.34.0, cvc5 1.3.4, and Z3 5.1.0:

- `lake build` and `lake build Test` pass.
- `cd MathlibTest && lake build` passes.
- `cd Doc/Verso && lake build && lake exe crush-docs` passes.
- The three updated benchmark scripts pass `bash -n`; the benchmark-report
  Python suite passes all 15 tests.

An initial concurrent test run reached the existing 10-second solver limit for
`cubeInvariantStep` in `Test/VelvetReconstruct.lean`. It passed without the full
compile load, with its timeout unchanged, and the subsequent full suite passed.
