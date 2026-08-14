# lean-crush Agent Guide

This document is the first-stop guide for an LLM coding agent working on
lean-crush. Read it before changing the translator, solver interface, or proof
reconstruction. The implementation and tests are authoritative; roadmap text may
describe planned work that has since changed.

Do not modify this file unless explicitly instructed to do so.

## Project Summary

lean-crush is a Lean 4 SMT hammer. The user writes `by crush`; the tactic collects
Lean propositions, translates them to typed SMT-LIB, invokes an external solver,
and either reports a counterexample or discharges the goal.

The project has three defining properties:

1. It handles higher-order Lean terms by defunctionalization or cvc5's native
   higher-order mode instead of rejecting every function-valued argument.
2. Its Lean-to-SMT translation is extensible through attributes, targeted
   lowerings, sort handlers, and an SMT-LIB term quotation.
3. Solver trust is explicit. Fast mode uses the auditable `Crush.crushSorry`
   axiom; reconstruction modes must produce a kernel-checked Lean term.

The root package intentionally has no Mathlib dependency. Mathlib integration
tests live in the separate `MathlibTest/` package, and Verso dependencies live in
`Doc/Verso/`.

External solvers are runtime tools, not Lean dependencies. The full suite expects
Z3 4.15.x and cvc5 1.3.x on `PATH`. Bitwuzla is also supported but receives less
test coverage.

## Read This First

Read these files in order:

1. `README.md` for the user-facing contract, examples, supported theories, and
   known limitations.
2. `Crush.lean` for the public modules exported by `import Crush`.
3. `Crush/Frontend/Tactic.lean` for the actual end-to-end control flow.
4. `Crush/Frontend/Config.lean` for every supported option and its semantics.
5. `Doc/OPTIMIZATIONS.md` before changing search bounds, instantiation,
   reconstruction, or query shaping.
6. `Doc/PLAN.md` for architecture history, soundness obligations, and roadmap.
   Use the source and tests when its status text disagrees with current code.
7. The closest file under `Test/` before modifying a subsystem.

The published user documentation is implemented under `Doc/Verso/`. User-visible
changes must keep the README and Verso manual synchronized.

## Execution Pipeline

`Crush.runCrush` in `Crush/Frontend/Tactic.lean` is the orchestration point:

1. Read `crush.*` options into `Crush.Config`.
2. Collect selected hypotheses, explicit hints, unfolding equations, library
   premises, and the negated goal as `Fact`s.
3. Try cheap kernel-checked closures before SMT, except when
   `crush.backend = "none"` requests full script emission.
4. Rewrite selected definitions with proof-producing normalization.
5. Specialize polymorphic facts through bounded monomorphization.
6. Generate bounded proof-producing ground instances for eligible facts.
7. Translate Lean `Expr`s into the typed SMT IR and validate the resulting script.
8. Run the configured solver under an enforced wall-clock timeout.
9. On `sat`, report a model; on `unknown`, fail honestly; on `unsat`, trust,
   replay an Alethe certificate, or reconstruct from the unsat core according to
   policy.

Ground instantiation may produce a smaller first query. Only `unsat` is conclusive
for that weakened query; `sat` and `unknown` retry with the complete quantified
fallback.

## Codebase Map

| Path | Responsibility |
|---|---|
| `Crush.lean` | Public root module and API exports |
| `Crush/Frontend/Config.lean` | Options and resolved `Config` |
| `Crush/Frontend/Tactic.lean` | Tactic syntax, hint parsing, pipeline, verdict handling |
| `Crush/Reify/Collect.lean` | Fact and premise collection with provenance |
| `Crush/Reify/Term.lean` | Reified STLC types and sanity-checking IR |
| `Crush/Translation/Monad.lean` | `TranslateM`, state, symbols, declarations, provenance |
| `Crush/Translation/Attr.lean` | Translation, lowering, result-lowering, and sort-handler registries |
| `Crush/Translation/Unfold.lean` | `@[crush_unfold]` and `@[crush_defeq]` |
| `Crush/Translation/Preprocess.lean` | Proof-producing selected-definition normalization |
| `Crush/Translation/Monomorphize.lean` | Polymorphic fact specialization |
| `Crush/Translation/Instantiate.lean` | Bounded proof-producing ground instantiation |
| `Crush/Translation/HOEncoding.lean` | Function sorts, closures, and application encoding |
| `Crush/Translation/Translate.lean` | Structural `Expr`-to-SMT translation and datatype emission |
| `Crush/Translation/Theories.lean` | Shared theory encodings and helpers |
| `Crush/Translation/DefaultLowerings.lean` | Built-in lowerings expressed through the public extension API |
| `Crush/SMT/` | Typed SMT IR, quotation, checker, printer, S-expressions, result parsing |
| `Crush/Solver/Process.lean` | Backend commands, process lifetime, timeout, response collection |
| `Crush/Solver/Alethe*.lean` | cvc5 Alethe parsing, term conversion, and checked step replay |
| `Crush/Solver/Reconstruct*.lean` | Unsat-core reconstruction, rules, and extension attribute |
| `Crush/Util/Profile.lean` | Per-phase profiling |
| `Test/` | Dependency-free core and solver integration tests |
| `Test/CaseStudies/` | Ported Lean-auto, Loom, Velvet, and Cashmere obligations |
| `MathlibTest/` | Optional Mathlib integration package |
| `Doc/Verso/` | Executable user manual and GitHub Pages build |
| `scripts/` | Corpus and LeanHammer benchmark harnesses |
| `.github/workflows/` | Core CI and documentation deployment |

`BenchmarkResults/` contains generated measurements. Do not commit benchmark
output unless the user explicitly requests a recorded result set.

## Translation Terminology

Translation is the complete recursive process that converts arbitrary Lean
expressions and types into SMT terms, sorts, declarations, and axioms.

A lowering is one extension hook inside translation. A
`@[crush_lower Some.constant]` handler is dispatched only for that application
head and may claim it by returning `some term` or defer by returning `none`.
`@[crush_translate]` is the general dynamic hook and runs before targeted
lowerings. `@[crush_lower_result T]` dispatches by result-family head, and
`@[crush_translate_sort]` changes a Lean type's SMT representation.

Built-in theory support should normally use the same public lowering
infrastructure available to downstream users. Keep operation lowerings and sort
lowerings representation-compatible.

## Non-Negotiable Invariants

### Soundness and trust

- `crush.trust = "reconstruct"` must never use `Crush.crushSorry`, an unreplayed
  solver certificate, an unchecked generated term, or an ambient hypothesis that
  was excluded from the selected facts.
- `reconstructOrTrust` may use the axiom only after a visible warning.
- Every accepted replay or reconstruction term must be free of `sorry` and
  metavariables and pass the Lean kernel checker before assignment.
- Unsupported semantics must remain uninterpreted or fail clearly. Never map a
  Lean operation to a merely similar SMT operation.
- Preserve SMT-LIB escaping, declaration order, sort correctness, and symbol
  identity. Expression-derived symbols use canonical structural keys, not pretty
  printed expressions.

### Extensibility

- General user translation handlers have first refusal over built-ins.
- Do not normalize a term in a way that bypasses a registered handler's intended
  semantics.
- Targeted lowerings must verify arity, argument types, and relevant typeclass
  dictionaries before assigning built-in SMT semantics.
- Prefer the `(smt| ...)` quotation over manually constructing nested
  `SMT.Term.symbApp` values.

### Completeness and scalability

- Monomorphization and instantiation are bounded searches. Fuel exhaustion may
  reduce completeness but must never strengthen the asserted facts unsoundly.
- Ground instantiation must retain a quantified fallback when its instance set is
  truncated or cannot safely replace its parent. Monomorphization may instead
  lose completeness by dropping an untranslatable polymorphic fact, but must
  report bound exhaustion.
- Keep bare `crush`, explicit `crush [...]`, and `crush [*, ...]` semantics
  distinct. An explicit list without `*` is a strict restriction.
- Reconstruction must operate on a closed implication built from selected/core
  facts, not inherit the original proposition context.
- Prefer datatype-generic algorithms based on Lean inductive metadata over
  hard-coded `Nat`, `List`, or constructor names.
- Use `SymM` where a hot loop performs repeated normalization, type inference, or
  definitional equality and can benefit from shared symbolic caches. Do not move
  ordinary one-shot metaprogramming into `SymM` without evidence.
- Search-bound changes require focused tests and downstream benchmark comparison.
  Read `Doc/OPTIMIZATIONS.md` first.

### Process and packaging

- Solver processes must have a hard wall-clock guard and guaranteed cleanup.
- `backend = "none"` is a translation-debugging mode. It must emit the complete
  script even when a pre-SMT Lean shortcut could close the goal.
- Keep `Crush/` and `Test/` independent of Mathlib.
- Do not add `sorry` to tests. Negative and known-limitation tests use
  `#guard_msgs`.

## Code Style

- Follow the existing Lean style: small named helpers, explicit types at public
  boundaries, early returns for unsupported cases, and descriptive names for
  state and proof objects.
- Keep module docstrings focused on contracts, architecture, and invariants that
  a reader cannot recover directly from the implementation.
- Do not over-document. Avoid comments that restate a declaration name, narrate
  straightforward control flow, or explain every assignment.
- Inline comments should concisely explain what a non-obvious block does. Include
  why only when it is necessary to preserve a subtle invariant, soundness
  condition, compatibility constraint, or measured performance decision.
- Comments must be self-contained and understandable from the checked-in code.
  Never carry conversation artifacts into source, including stage markers, goal
  markers, temporary plans, agent notes, user-request summaries, or references
  such as "the issue discussed above."
- Describe permanent behavior rather than the sequence by which a change was
  developed. Put historical rationale in `Doc/PLAN.md` or
  `Doc/OPTIMIZATIONS.md` only when it remains relevant to future maintenance.
- Keep comments synchronized with behavior. A stale detailed comment is worse
  than no comment.
- Prefer the repository's existing terminology (`translation`, `lowering`,
  `reconstruction`, `fact`, and `unsat core`) and use ASCII unless the surrounding
  file already requires other notation.

## Where to Make a Change

| Task | Start here | Typical tests |
|---|---|---|
| Tactic syntax or hint semantics | `Crush/Frontend/Tactic.lean`, `Crush/Reify/Collect.lean` | `Test/Hints.lean`, `Test/Premises.lean` |
| New option | `Crush/Frontend/Config.lean` | `Test/Smoke.lean`, relevant subsystem test, Verso configuration |
| Built-in operation or theory | `Crush/Translation/DefaultLowerings.lean`, `Crush/Translation/Theories.lean` | `Test/Theories.lean`, `Test/Regression.lean` |
| User extension API | `Crush/Translation/Attr.lean`, `Crush/Translation/Builtins.lean`, `Crush/SMT/Quote.lean` | `Test/Extension.lean`, `Test/ArrayTheory.lean` |
| Datatypes or structural translation | `Crush/Translation/Translate.lean` | `Test/DatatypeWF.lean`, `Test/Recursive.lean`, `Test/Monomorphize.lean` |
| Higher-order encoding | `Crush/Translation/HOEncoding.lean`, `Crush/Translation/Translate.lean` | `Test/HigherOrder.lean`, `Test/Cvc5.lean`, `Test/MonoStress.lean` |
| Polymorphic facts | `Crush/Translation/Monomorphize.lean` | `Test/LemmaMono.lean`, `Test/Monomorphize.lean` |
| Quantifier instantiation | `Crush/Translation/Instantiate.lean` | `Test/Instantiate.lean`, `Test/Cashmere.lean` |
| SMT syntax or printing | `Crush/SMT/Syntax.lean`, `Crush/SMT/Quote.lean`, `Crush/SMT/Print.lean`, `Crush/SMT/Check.lean` | `Test/SMTCheck.lean`, `Test/Extension.lean` |
| Solver lifecycle or backend | `Crush/Solver/Process.lean` | `Test/Smoke.lean`, `Test/Cvc5.lean` |
| Alethe replay | `Crush/Solver/Alethe*.lean` | `Test/Alethe.lean`, `Test/AletheReplay.lean` |
| Core reconstruction | `Crush/Solver/Reconstruct*.lean` | `Test/Reconstruct.lean`, `Test/ReconstructHard.lean`, `Test/VelvetReconstruct.lean` |
| Performance heuristic | Relevant phase plus `Crush/Util/Profile.lean` | Focused test, full suite, corpus benchmarks |

## Development Workflow

Inspect the working tree before editing and preserve unrelated user changes:

```sh
git status --short
```

Build the library:

```sh
lake build
```

Run a focused module while iterating:

```sh
lake build Test.Extension
lake build Test.Instantiate
lake build Test.Reconstruct
```

Run the complete dependency-free suite before finalizing a core change:

```sh
lake build Test
```

Run optional Mathlib integration after changes to theories, unfolding, coercions,
or polymorphism:

```sh
cd MathlibTest
lake exe cache get
lake build
```

Build and render the user manual after documentation or public API changes:

```sh
cd Doc/Verso
lake build
lake exe crush-docs
```

Useful debugging controls include:

```lean
set_option crush.trace.script true
set_option crush.save "/tmp/query.smt2"
set_option crush.backend "none"
set_option crush.profile true
set_option trace.crush.result true
```

Use `backend = "none"` to inspect translation independently of solver behavior.
Run the saved script directly with the configured solver when distinguishing a
translation bug from solver incompleteness.

For search or performance changes, use the scripts and protocol in
`Doc/OPTIMIZATIONS.md`. Record solver versions, repository commits, trust mode,
timeouts, dirty state, coverage, matched-goal latency, and tail latency. A faster
warm build is not evidence of a faster tactic.

## Testing Expectations

- Add the smallest regression that would have failed before the change.
- Test both success and sound refusal when a boundary is semantic.
- Use `crush.trust "reconstruct"` and `#print axioms` when the claim concerns
  checked proof production.
- Use `crush.reconstruct "alethe"` when a test must prove certificate replay
  itself succeeded rather than silently falling back to core reconstruction.
- Pin false goals and known gaps with `#guard_msgs(error, substring := true)`.
  Match stable prefixes, not solver-specific model details.
- Test custom handlers against precedence and sort compatibility, not merely
  registration.
- Test multiple type instantiations for polymorphic changes and noncanonical
  typeclass instances for overloaded operations.
- Run both Z3 and cvc5 paths when touching higher-order translation, process
  handling, result parsing, or reconstruction.

## Documentation and Review Checklist

Before finishing:

1. Confirm no unrelated files were reverted or generated artifacts added.
2. Run focused tests, then the appropriate full suites.
3. Check whether README, Verso, option docs, `Doc/PLAN.md`, or
   `Doc/OPTIMIZATIONS.md` must change.
4. Review the trust boundary and prove that every new trusting behavior is
   explicit.
5. Review failure paths for retained fallbacks, restored metavariable state,
   process cleanup, and actionable diagnostics.
6. Benchmark any change that raises a bound, broadens premise selection, adds
   eager instantiation, or introduces a new reconstruction search branch.
