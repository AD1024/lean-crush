import VersoManual

open Verso.Genre Manual

#doc (Manual) "Benchmarks" =>
%%%
tag := "benchmarks"
%%%

The benchmark harness separates solver verification from checked proof
reconstruction. This distinction prevents a reconstruction limitation from
being reported as a translation or solver failure.

The complete numeric tables, tested revisions, machine configuration, and
interpretation notes are in
[BENCHMARKS.md](https://github.com/AD1024/lean-crush/blob/main/BENCHMARKS.md).
The
[script guide](https://github.com/AD1024/lean-crush/blob/main/scripts/README.md)
gives self-contained reproduction commands. The
[recorded inputs](https://github.com/AD1024/lean-crush/tree/main/scripts/benchmark-data)
regenerate these exact figures and retain the per-VC baseline records.

# Headline Comparison

The headline figure compares Auto, Duper, trusted Crush, and `grind` on one
fixed set of VC occurrences for each corpus. Trusted Crush sets
`crush.trust = "trust"`: it measures collection, specialization, translation,
and SMT solving without requiring post-solver proof reconstruction. The other
backends retain their normal proof and trust policies, so the table reports
those differences rather than treating every row as the same trust guarantee.

`Auto` is the lean-auto backend configured by the host project; in LeanHammer
this is its Auto preprocessing and monomorphization pipeline feeding Duper.
`Duper` invokes Duper directly after host preprocessing. The PLean lane gives
each Duper attempt one second of saturation and 20,000 heartbeats, while
leaving the generated file uncapped so every VC is attempted. `grind` is
Lean's kernel-checked tactic; PLean uses a pure-`grind` backend guarded against
external solver calls. The `Crush` legend always denotes the trusted SMT lane
in this figure, not one of the checked reconstruction strategies below.

`Solved / total` uses the fixed corpus total as its denominator for every
backend. `Failed` means the backend was attempted but did not close the VC.
`Missing` means no complete attempt record exists, for example because a
generated file terminated early. Both count as unsolved for coverage, but
missing records are excluded from timing statistics. Valid headline runs must
have zero missing records; every lane in the published comparison has zero.

The figures show LeanHammer, Cashmere, Velvet, and PLean. Loom is measured and
kept in the recorded reports, but its four VCs are too few for a coverage bar
to carry a meaningful percentage, so the figures omit it.

![Verification coverage by corpus and backend](../../figures/coverage.svg)

The outcome figure partitions every backend's fixed workload into exactly four
categories. `Success` means the VC was closed. `Translation error` requires an
explicit diagnostic that the backend could not translate or encode the goal.
`Timeout` requires an explicit wall-clock, heartbeat, or saturation-limit
diagnostic. `Failed to prove` contains all remaining unsuccessful attempts,
including solver `sat` or `unknown`, exhausted proof search, and ordinary
tactic failures. It does not hide missing attempts: the plotting script rejects
a bar unless its four segments sum to the corpus total.

![Verification outcomes by corpus and backend](../../figures/outcomes.svg)

# Proof Reconstruction

Proof reconstruction is measured separately from the headline comparison. Its
denominator is the subset of successful trusted-verification VCs whose profile
records that SMT actually returned `unsat`; selected facts and goals closed by
checked pre-SMT reconstruction are reported as verify-lane successes but are
not treated as certificate-reconstruction attempts. Core reconstruction
re-proves an unsat core with Lean tactics. Alethe reconstruction replays cvc5's
refutation step by step. The portfolio first attempts Alethe and then falls
back to core reconstruction.

These plots retain an earlier reconstruction-focused run. They characterize
the checked strategies and are not extra Crush rows in the latest headline
comparison.

![Checked proof reconstruction among SMT-verified VCs](../../figures/reconstruction.svg)

Failure modes distinguish missing or malformed certificates, unsupported
Alethe rules or terms, solver `sat` and `unknown` results, and failures of
core-directed Lean reconstruction. `not-attempted` means an earlier failure or
declaration heartbeat stopped the generated file before that VC reached the
strict lane; it is not classified as a reconstruction attempt.

Each pie aggregates failure records from Core, Alethe, and Portfolio for one
corpus. An SMT-cohort VC can therefore contribute one record per strict lane;
the lane-specific counts remain available in `reconstruction-failures.tsv` and
the tables in
[BENCHMARKS.md](https://github.com/AD1024/lean-crush/blob/main/BENCHMARKS.md).

![Proof reconstruction failure records by corpus](../../figures/reconstruction-failures.svg)

# Comparing Reconstruction With lean-smt

The plots above compare Crush's own strategies. The harnesses also measure
[lean-smt](https://github.com/ufmg-smite/lean-smt), which translates a goal,
calls cvc5, and replays the Alethe certificate in Lean, against Crush's strict
Alethe lane and its reconstruction portfolio. Because no tool controls the
denominator of a cross-tool comparison, that report uses the exact VC-identity
intersection of the compared lanes, and it separates two questions: how many
matched VCs each lane closed with a kernel-accepted Lean proof by any route,
and how many certificates each lane replayed within the narrower SMT-`unsat`
cohort.

lean-smt reports an Alethe rule it cannot replay by leaving that step as an
open goal rather than by failing, so the harness checks the remaining goals
itself and records those VCs as a rule gap instead of counting them solved.
The comparison covers every corpus. Only LeanHammer's pinned revision already
requires lean-smt; the others get it from a recorded patch that adds the
dependency to the pinned revision, after which the harness checks that no
revision the corpus already pinned moved. Run it with
`benchmark-reconstruction.sh`; the
[benchmark script guide](https://github.com/AD1024/lean-crush/blob/main/scripts/README.md)
documents the reports it writes.

# Time Breakdown

Profiler records use nanosecond counters around the major Crush phases. The
stacked bars show the share of profiler-accounted time, not process wall time.
Solver startup and communication are included in `solve`; certificate parsing,
step replay, proof assembly, and final kernel checking are included in
`replay`.

![Crush profiler time grouped by phase](../../figures/phase-breakdown.svg)

# Alethe Replay Scaling

Certificate size is measured primarily by the number of parsed Alethe
commands. The plot includes only successful strict Alethe replays and averages
repeated measurements for each VC. Its replay-time axis is logarithmic because
the samples span several orders of magnitude. The dashed least-squares line,
Pearson correlation, and slope are computed in the original linear units.

![Alethe replay time against parsed certificate commands](../../figures/alethe-replay-scaling.svg)

These measurements characterize the recorded corpus and machine. Use multiple
repeats before treating small timing differences as performance claims.
