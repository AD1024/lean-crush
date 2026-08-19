# Optimization and Search Heuristics

This document records the bounded searches and query-shaping heuristics used by
lean-crush. These choices are part of the performance design: changing one can
improve coverage while causing an exponential regression on unrelated goals.
Keep this file synchronized with the implementation and benchmark changes against
the downstream corpora before raising a bound.

## Pipeline strategy

The tactic tries to make each later phase smaller:

1. Filter selected library premises by a speculative `apply` to the goal.
2. Close exact selected facts and small checked proof obligations before SMT.
3. Normalize selected definitions and reducible predicates in Lean.
4. Monomorphize and instantiate explicit quantified facts under configurable bounds.
5. Emit the SMT query, using recursive definitions rather than quantified recursive
   equations where possible.
6. Use the unsat core to reconstruct from only the facts the solver needed.

Every speculative Lean proof attempt saves and restores metavariable state on failure.
An accepted proof may contain neither `sorry` nor unresolved expression or universe
metavariables, and is kernel-checked before assignment to the original goal.

`crush.backend "none"` deliberately skips the pre-SMT proof shortcuts. Its purpose is
script emission and translation debugging, so it must still run the complete translation
pipeline even when Lean could close the goal first.

## Premise and quantifier control

Premise selection asks Lean's `LibrarySuggestions` engine for up to four times the
requested result count, capped at 128, then keeps only suggestions that can
speculatively apply to the current goal. The final count remains bounded by
`crush.premises.max` (default 32). This avoids filling the useful prefix with
high-ranked theorems that merely share vocabulary with the goal.

Lemma monomorphization is a saturating pass bounded by:

| Control | Default | Purpose |
|---|---:|---|
| `crush.mono.fuel` | 512 | Maximum generated type instances |
| `crush.mono.rounds` | 8 | Maximum saturation rounds |

Only genuine data types are candidates: propositions, `Sort`, and function types are
excluded. This prevents polymorphic lemmas from being instantiated at propositions or
arrows and avoids large irrelevant cross-products. Setting either option to zero
disables lemma monomorphization.

Proof-producing ground term instantiation is bounded separately:

| Control | Default | Purpose |
|---|---:|---|
| `crush.inst.fuel` | 128 | Maximum generated ground instances |
| `crush.inst.rounds` | 3 | Maximum saturation rounds |

Instances are generated in one `SymM` session so repeated symbolic normalization,
groundness checks, and definitional equality tests share caches. A quantified parent is
removed only when its useful ground consequences were generated without exhausting the
budget. Otherwise the quantified fallback is retained. Setting either option to zero
disables this pass.

## Pre-SMT checked proofs

Before translation, Crush uses only the selected facts to try several cheap,
kernel-checked closures:

- exact definitional equality with a selected fact;
- direct application of a selected quantified invariant or explicit helper;
- a constructor-guided witness for a top-level existential;
- one constructor split for a small logically structured target;
- empty-datatype elimination;
- full bounded reconstruction only for function-valued existential witnesses.

The proof problem is abstracted into a closed implication containing exactly the
selected facts. This preserves the strict semantics of `crush [h, lemma]`: omitted
ambient propositions cannot leak into reconstruction.

Pre-SMT limits are:

| Search dimension | Bound |
|---|---:|
| Selected facts allowed for full `simp_all` | 6 |
| Target depth allowed for pre-split full `simp_all` | 8 |
| Top-level selected rules tried | 16 |
| Subgoals from one selected rule | 16 |
| Premise rule-recursion fuel | 0 |
| Constructor split depth | 1 |
| Total pre-split branch budget | 24 |

Larger contexts use `simp_all only`, which retains definitional reduction without
allowing a speculative global simplifier pass to scale with arbitrary solver hints.
Pre-SMT paths never invoke `grind`, and constructor splitting uses zero rule fuel.

## Core-directed reconstruction

After an `unsat` verdict, reconstruction builds a fresh closed implication from the
unsat-core proofs and the goal. Local data parameters that occur in that implication
are abstracted; propositions outside the core are absent.

Replay and reconstruction compute the dependency closure of those parameters by
following only referenced local declarations, in declaration order. They do not filter
the complete ambient context for every proof step, so excluded hypotheses do not cause
per-step context scans.

The search order is:

1. Unpack conjunction hypotheses and same-constructor equalities.
2. Apply local quantified rules and `@[crush_reconstruct]` rules indexed by conclusion.
3. Try the fixed finisher portfolio (`grind`, `omega`, `simp_all`, function
   extensionality, substitution, `decide`, and `rfl` variants).
4. Synthesize a constructor-shaped existential witness.
5. Split finite enumerations exhaustively within a branch budget.
6. Try a shallow general constructor split.

Rules are indexed with a discrimination tree instead of being added wholesale to
`grind`. Local rules are filtered by conclusion head and by a speculative `apply`.
Premises containing unanchored metavariables are rejected before expensive tactics can
explore arbitrary instantiations.

Core search limits are:

| Search dimension | Bound |
|---|---:|
| Conjunction decomposition fuel | 8 |
| Constructor-equality decomposition fuel | 8 |
| Normal backward-rule recursion fuel | 2 |
| Applicable local rules tried per goal | 16 |
| Equality pairs tried for `by_cases` | 3 |
| Reducible constants collected | 8 |
| Reducible-normalization depth | 8 |

Equality splitting is attempted only when a quantified local rule already applies to the
target. Its branches use `omega`, `simp_all`, `rfl`, and `decide`; global `grind` is
intentionally excluded.

## Alethe replay

Alethe clauses retain their top-level literal boundaries; Boolean `or` inside one SMT
literal is not flattened into the enclosing clause. Replay validates each named source
assumption before derived steps can consume it.

Structural proof construction runs before tactic search for resolution, weakening,
transitivity, excluded-middle clauses, conjunction projection, and `Iff` implication
clauses. Wide or multiply referenced resolution results are shared through checked
auxiliary declarations. Only remaining theory-specific steps enter the tactic portfolio.

This ordering is profiler-driven. On an isolated width-8 bit-vector comparison,
structural replay reduced replay from 5.50-5.59 seconds to 1.09-1.13 seconds. Across two
detailed-profile runs, `grind` fell from 196 calls and 5.94 seconds to 44 calls and
0.21 seconds. The measured bottleneck was repeated tactic elaboration, not symbolic
normalization, so this path remains in `MetaM` rather than adding a `SymM` boundary.

## Datatype splitting

Constructor search is datatype-generic. It does not inspect names such as `Nat.succ`;
it asks the environment for the inductive declaration and uses Lean's `cases`.

| Search dimension | Bound |
|---|---:|
| Candidate local values | 8 |
| Constructors on one candidate datatype | 16 |
| Branches created by one split | 16 |
| Logical/recursor target structural depth | 64 |
| Other target structural depth | 24 |
| Post-SMT finite-enum split depth | 6 |
| Post-SMT finite-enum branch budget | 256 |
| Post-SMT general split depth | 2 |
| Post-SMT general branch budget | 64 |

Only locals that occur in the target are candidates. For atomic targets, candidates
must additionally have the type of a target argument; this avoids splitting datatypes
hidden inside unrelated terms. Logical wrappers are classified before weak-head
normalization, so a `Not` or `Ne` target can still split constructor-bearing values
nested in its operands. Field-free finite enumerations receive the deeper search because
repeated splits cannot expose recursive fields and become an accidental induction
procedure.

## Existential witnesses

Witness synthesis starts from target subterms of the required type, then closes the pool
under constructors for two rounds. Constructors with fields are tried before nullary
constructors because `succ t`, `some x`, and `cons x xs` are usually more informative
than defaults.

| Search dimension | Bound |
|---|---:|
| Target subterms collected | 48 |
| Witness candidates retained | 32 |
| Constructor-closure rounds | 2 |
| Constructor fields synthesized | 3 |
| Compatible terms tried for one field | 12 |
| Applications returned per constructor search | 16 |

General `grind` is not run for every witness candidate. Candidate bodies use assumption,
`rfl`, constructor reduction, `omega`, bounded simplification, `decide`, and the same
bounded reconstruction-rule mechanism.

## Translation heuristics

- `@[crush_lower target]` handlers are indexed by head constant. General dynamic
  `@[crush_translate]` handlers remain priority-ordered because they may match any term.
- Predicates marked `@[reducible]` are normalized with constructor-specific equations
  in proof-producing preprocessing. Their equations are not asserted as recursive
  quantified SMT axioms.
- Recursive datatype well-formedness predicates use `define-fun-rec` or
  `define-funs-rec`. This avoids the quantifier-instantiation loops caused by universal
  defining axioms.
- Unsupported indirect recursive datatype groups remain opaque instead of emitting an
  invalid or incomplete recursive declaration.
- Overloaded built-in operations are lowered only after checking the exact expected
  dictionary, a lawful `BEq`, or a deliberately constrained instance head. This avoids
  assigning built-in SMT semantics to user-defined operations.
- Function symbols and sorts use canonical structural identities rather than
  potentially non-injective pretty-printed types.
- Solver responses are parsed once. The S-expression scanner examines UTF-8 bytes
  directly because SMT-LIB structural characters and whitespace are ASCII; atoms are
  extracted only after their complete spans are known.
- SMT string lowerings claim only operations whose Lean and SMT semantics agree.
  Replacement, character patterns, byte positions, numeric parsing, and lexicographic
  order remain uninterpreted where the domains or edge cases differ.

## Reproducing the comparisons

Install `z3` and `cvc5`, then run the corpus harness directly:

```sh
REPEATS=1 \
TIMEOUT=5 \
SOLVER=cvc5 \
CRUSH_TRUST=reconstruct \
MAX_HEARTBEATS=1000000 \
scripts/benchmark-corpora.sh
```

The harness builds local Crush, provisions the pinned LeanHammer, Loom, and
Velvet revisions under `BenchmarkResults/sources`, and builds their Lake
packages. Override `HAMMER_REPO`, `LOOM_REPO`, or `VELVET_REPO` to use existing
checkouts. Set `Z3_BIN` and `CVC5_BIN` to executable paths when they are not on
`PATH`.

The script creates detached worktrees for:

- the pinned auto, Duper, and Crush Loom revisions;
- the pinned auto, Duper, and Crush Velvet revisions;
- the LeanHammer checkout's `duper-only`, `auto-duper`, `crush-only`,
  `aesop-auto-duper`, and `aesop-crush` profiles.

Cashmere is benchmarked from the Loom branches. No source checkout is modified.
Set the corresponding `LOOM_*_REF` or `VELVET_*_REF` variable to compare
different commits. For less noisy timing, use at least `REPEATS=3`.

Focused runs avoid rebuilding unrelated corpora:

```sh
RUN_LEANHAMMER=false RUN_LOOM=false RUN_CASHMERE=false \
  scripts/benchmark-corpora.sh

RUN_LEANHAMMER=false RUN_LOOM=false RUN_VELVET=false \
  scripts/benchmark-corpora.sh

RUN_LEANHAMMER=false RUN_LOOM=false RUN_CASHMERE=false \
VELVET_CASES="Velvet/Examples/GCD.lean Velvet/Examples/IsSorted.lean" \
  scripts/benchmark-corpora.sh
```

Use `RUN_AUTO=false`, `RUN_DUPER=false`, or `RUN_CRUSH=false` for selected
backend profiling. Use
`CRUSH_PROFILE=true` to include Crush's per-phase breakdown in logs. The standalone
LeanHammer harness is:

```sh
REPEATS=3 scripts/benchmark-leanhammer.sh
```

The PLean comparison is also self-provisioning:

```sh
RUN_DUPER=true \
REPEATS=1 \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=60 \
scripts/benchmark-plean.sh
```

Its Duper branch is an opt-in scalability stress test because the larger files
do not complete in practical time. This command runs every file separately
with a 60 CPU-second limit:

```sh
RUN_AUTO=false \
RUN_CRUSH=false \
RUN_DUPER=true \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=60 \
REPEATS=1 \
scripts/benchmark-plean.sh
```

Each run prints two tables and writes the complete data under a timestamped
`BenchmarkResults/corpora-*` directory:

| File | Contents |
|---|---|
| `metadata.tsv` | Repository commits, toolchains, solver, trust mode, and dirty state |
| `results.tsv` | Per-obligation status, failure category, tactic time, and goal hash |
| `runs.tsv` | Per-file wall time, exit status, obligation count, and truncation status |
| `summary.tsv` | Coverage and aggregate attempted-VC timing by corpus/backend |
| `matched-summary.tsv` | Coverage and timing on the three-backend VC intersection |
| `comparison.tsv` | Pairwise matched-VC outcomes and mean times where both backends solved |
| `logs/` | Complete elaborator and solver output |

Compare matched VCs in `comparison.tsv`; raw corpus totals can differ when the backend
branches contain different generated obligations. Preserve `metadata.tsv` when sharing
numbers so the branch commits and dirty local Crush state are auditable.

`BenchmarkResults/` is intentionally not versioned. Evaluate coverage, matched-goal
latency, and tail latency together: a higher bound that closes one obligation but adds
speculative saturation to every goal is usually a regression.
