# Alethe Replay Coverage

This document tracks proof-replay completeness. It is intentionally narrower than
SMT-LIB completeness.

The supported universe is:

1. SMT terms that lean-crush can currently emit;
2. Alethe certificates produced by cvc5 1.3.4 with lean-crush's proof options; and
3. proof steps that can be translated back to Lean and kernel-checked.

User lowerings can emit arbitrary SMT terms, and cvc5 may change its internal proof
language between releases. There is therefore no meaningful claim that replay is
complete for all SMT-LIB or all Alethe.

## Status Classes

Every probe belongs to exactly one class:

| Class | Meaning |
|---|---|
| `replayed` | cvc5 emitted a certificate and lean-crush reconstructed a kernel-checked proof |
| `no-certificate` | cvc5 proved `unsat` but rejected Alethe serialization |
| `parse-gap` | cvc5 emitted a certificate that the S-expression or Alethe parser rejected |
| `term-gap` | a certificate term or sort could not be translated back to Lean |
| `rule-gap` | terms translated, but a concrete proof step could not be proved from its premises |
| `kernel-reject` | replay built a term that Lean's kernel rejected |

`no-certificate` is a solver boundary, not a lean-crush implementation task. Such
probes remain in the suite so a cvc5 upgrade that starts producing a certificate is
noticed and reclassified.

## Current Matrix

| Fragment | Query translation | Alethe replay | Notes |
|---|---:|---:|---|
| Propositional logic | yes | replayed | Includes structural clauses and nested multi-assumption subproofs |
| Uninterpreted functions and equality | yes | replayed | Includes congruence chains and defunctionalized application |
| `Int` linear arithmetic | yes | replayed | |
| `Int` nonlinear arithmetic | yes | replayed | Requires cvc5's DSL-rewrite proof granularity |
| `Int` division and modulo | yes | replayed | Lean's zero-divisor behavior is guarded in the query |
| `Nat` arithmetic | yes | replayed | Recovered from the nonnegative `Int` encoding |
| Quantifiers | yes | replayed | Live tests cover `forall_inst`, `bind`, and `sko_forall`; the `sko_ex` handler is implemented but not emitted by current cvc5 probes |
| Strings | partial | replayed | Length, append, empty, prefix, suffix, and containment |
| Bit-vectors | partial | replayed | Arithmetic, signed/unsigned comparisons, shifts, rotations, extraction, extension, concatenation, and unsigned integer conversions |
| Signed bit-vector-to-`Int` | yes | no-certificate | cvc5 reports unsupported `sbv_to_int` |
| Datatype injectivity | yes | replayed | |
| Finite-datatype exhaustiveness | yes | no-certificate | cvc5 reports `DUMMY_SKOLEM` |
| Finite arrays | yes | no-certificate | cvc5 reports `DUMMY_SKOLEM` |
| Defunctionalized higher-order terms | yes | replayed | |
| Native higher-order terms | cvc5 only | no-certificate | cvc5 reports unsupported higher-order proof elements |
| User-defined operators | user-defined | replayed | `register_crush_replay term` or `@[crush_replay "operator"]` supplies ordinary and indexed inverse decoding |

## Coverage Tests

A theory is covered only when all applicable layers are tested:

1. **Semantic lowering test.** A nontrivial Lean theorem exercises the intended
   lowering, plus a false-statement test checks that the encoding does not strengthen
   the source semantics.
2. **Typed SMT test.** The generated script passes `SMT.checkScript`.
3. **Certificate feature test.** The live cvc5 certificate is inventoried. Query
   occurrence alone does not count because preprocessing may remove the operator or
   cvc5 may prove the result through a different representation.
4. **Decoder fixture.** A certificate term containing each observed operator is
   translated to a well-typed Lean expression.
5. **Alethe-only integration test.** The theorem runs with
   `crush.reconstruct "alethe"` so the core-directed fallback cannot hide a replay
   failure.
6. **Kernel boundary test.** The accepted theorem's axioms do not include
   `Crush.crushSorry`.

Tests should use symbolic operands and a property that depends on the target operator.
Closed computations are insufficient because Lean or cvc5 may evaluate the operation
before replay.

Pinned certificate fixtures make parser and decoder tests deterministic. Live cvc5
tests catch changes in solver output. Both are needed: fixtures alone miss solver
changes, while live tests alone can stop exercising an operator after a solver rewrite.

## Replay Strategy

Replay validates source assumptions before derived steps can consume them. Resolution,
weakening, transitivity, excluded-middle clauses, conjunction projections, and
`Iff` implication clauses use structural Lean proof terms. Remaining concrete steps use
a small tactic portfolio and pass the kernel boundary before reuse. The assembled proof
and any generated auxiliary declarations are checked again before goal assignment.

Profiler-guided structural replay matters for bit-blasted certificates. On an isolated
width-8 unsigned-comparison probe, it reduced replay from 5.50-5.59 seconds to
1.09-1.13 seconds by avoiding repeated `grind` calls on propositional clauses.

## Work Queue

1. Add a live `sko_ex` regression if the pinned cvc5 version emits that rule.
2. Re-run the no-certificate probes when the pinned cvc5 version changes.
3. Inventory and pin newly observed operators, indexed operators, sorts, and rules as
   translation theories expand.

Arrays, finite-datatype exhaustiveness, signed bit-vector-to-integer conversion, and
native higher-order proofs are skipped until cvc5 emits Alethe for them.

## Future Theory Priorities

New translation theories should be added only with an exact Lean semantics and a viable
checked-reconstruction path.

1. Fixed-width `UInt8`/`UInt16`/`UInt32`/`UInt64` operations can reuse the existing
   bit-vector theory and proof infrastructure.
2. Standalone `Char` can use a bounded codepoint encoding. Relating it to SMT strings
   needs care because Lean and SMT-LIB admit different character domains.
3. Exact rational or real arithmetic is useful once a dependency-free Lean carrier and
   division-by-zero semantics are selected.

Floating point, regular expressions, sets, bags, relations, and general sequence theory
remain workload-driven. They should not acquire speculative replay tables before a
case study demonstrates both demand and certificate availability.
