# CPC replay implementation plan

The replay engine will share term decoding, checked proof construction, and scope
management across certificate formats. Parsers retain each format's rule names;
inference handlers are indexed by both format and rule. SMT term decoders remain
shared because custom lowerings have the same meaning in either certificate.

## Steps

- [x] Extract the common replay infrastructure and add
  `register_replay_rule Alethe << ... >>` and
  `register_replay_rule CPC << ... >>`, including format-specific attributes.
  Preserve the existing Alethe registration spelling as a compatibility alias.
- [ ] Parse cvc5 CPC certificates with explicit conclusions, including shared
  terms, bound variables, assumptions, and scoped subproofs. Unsupported forms
  must decline without accepting unproved assumptions.
- [ ] Add CPC handlers through the public registry, reusing checked arithmetic,
  logical, and theory proof helpers. Keep dispatch isolated by format.
- [ ] Add `crush.reconstruct "cpc"` (also accept `"CPC"`), configure cvc5's proof
  output, and select the matching parser and handlers. Alethe and CPC both use
  core-guided fallback by default; `crush.reconstruct.fallback false` requires
  certificate replay and skips early closure for reliable replay testing.
- [ ] Add parser, registry, scope, soundness, fallback, and live cvc5 tests.
  Reuse existing Alethe obligations for both formats and check proof axioms.
- [ ] Update the README and executable Verso manual; build the library, full
  test suite, and manual, then review the final diff.

## Validation boundaries

Every accepted inference and final proof remains checked by Lean. Replay uses
only selected source facts and premises in scope, and restores state on failure.
Proof rules and certificate conclusions are untrusted inputs. Missing rules,
unsupported terms, malformed certificates, and solver serialization errors may
trigger checked core reconstruction, never an implicit trusted discharge.

The default `auto` mode continues to request Alethe, preserving its solver query
and search behavior. CPC is opt-in. No search bounds are increased.
