import VersoManual

open Verso.Genre Manual

#doc (Manual) "Benchmarks" =>
%%%
tag := "benchmarks"
%%%

These figures are regenerated from the raw measurements in
`BenchmarkResults/paper/`, also preserved in the
[evaluation archive](https://github.com/AD1024/lean-crush/blob/main/scripts/benchmark-data/eval-data.zip).
They cover the same 754 verification conditions (VCs): Curated (20), Cashmere
(38), Velvet (504), and PLean (192).
The archive also retains Loom's four VCs, omitted from the figures.

The archive contains `curated/`, `corpora/`, and `plean/` reports, with corpus
revisions, options, and dirty-tree provenance in `metadata.tsv`. The
[script guide](https://github.com/AD1024/lean-crush/blob/main/scripts/README.md)
documents reproduction with `run-experiments.sh`. These are recorded results,
not a fresh run of the current commit. Timings are individual measurements, so
small differences and results near the solver timeout need repeated runs.

# Headline Comparison

The comparison includes Auto, Duper, lean-smt, `grind`, and two Crush policies:

* *SMT trusted* uses `crush.trust "trust"` and requires no post-solver proof.
* *Kernel-checked* uses `crush.trust "reconstruct"` with the `"auto"`
  reconstruction portfolio: Alethe replay followed by core reconstruction.

Auto uses each host project's lean-auto backend; Curated invokes lean-auto
with Duper as its first-order prover. Duper runs directly after host
preprocessing. lean-smt translates to cvc5 and reconstructs its certificate.
Each backend retains its own proof policy and preprocessing.

On these 754 VCs, trusted Crush closes *709 (94.0%)* and the checked portfolio
closes *692 (91.8%)*. Each corpus uses the same VC identities across lanes,
and every lane has zero missing attempts.

The curves show how many VCs finish within the per-VC time on the logarithmic
horizontal axis. Time is measured around each tactic invocation, including
translation and any proof reconstruction. The dashed line marks the corpus's
total workload; failed VCs never enter a curve. Repeated measurements are
averaged per VC.

![Verification coverage over time by corpus and backend](figures/coverage-over-time.svg)

Outcomes partition the whole workload: success, explicit translation error,
explicit timeout, and other failures to prove. The last category includes
`sat`, ordinary `unknown`, exhausted proof search, and reconstruction failures.
Missing attempts would count as unsolved coverage, but have no attempt time.

![Verification outcomes by corpus and backend](figures/outcomes.svg)

# Proof Reconstruction

The reconstruction reports distinguish two denominators:

* *All VCs* measures checked proof coverage, including early Lean proofs.
* *SMT cohort* contains the *503* successful trusted-lane VCs whose profiler
  records SMT `unsat`. It excludes trusted-lane successes closed before SMT.

The checked-proof curves compare lean-smt, Alethe, and the portfolio using the
harness's final VC verdict. The Crush lanes finish
*246 / 754* in the Alethe lane and *692 / 754* in the portfolio.
This includes host-side Lean proofs and successes after failed intermediate
attempts. Core alone was not measured; its absence does not mean zero coverage.

![Checked proof coverage over time by corpus and tool](figures/reconstruction-over-time.svg)

Attribution to a reconstruction route is more conservative: every recorded
attempt must have an outcome accepted by that lane. Within the SMT cohort,
the reporter attributes *69 / 503* to Alethe and *482 / 503* to the portfolio.
An unsuccessful attempt can prevent attribution even when the host later
closes the VC with a checked proof.

The failure chart explains missing attribution within the SMT cohort, with
one record per lane and VC. It includes recovered attempts; it is not a count
of unproved VCs. This snapshot measures Alethe and Portfolio, so one VC can
appear twice. Most failures are cvc5 certificate errors. `term-gap` and `rule-gap`
identify decoding and Lean inference failures; the remaining categories cover
core failures, timeouts, and other unsuccessful attempts. `not-attempted`
records mean the strict lane never reached the VC.

![Reconstruction failure records within the SMT cohort](figures/reconstruction-failures.svg)

# Comparing Reconstruction With lean-smt

`reconstruction-comparison.tsv` compares lean-smt, strict Alethe, and the
portfolio on their exact VC-identity intersection. It reports completed checked
proofs by any route, plus reconstruction attribution within the
trusted lane's SMT cohort. Timing on VCs proved by every compared lane is
reported separately from timing on each lane's own successful set.

The harness checks for remaining goals: an unsupported lean-smt replay rule
that leaves a goal open is a failure, even if the tactic did not throw an error.
See the archive's per-VC measurements for the corresponding attempts.

# Time Breakdown

The bars show shares of profiler-accounted Crush time. `solve` includes solver
startup, communication, and retrieval of requested cores and proofs. `replay`
includes certificate parsing, step replay, proof assembly, and final kernel
checking. These counters do not measure the whole Lean process.

![Crush profiler time grouped by phase](figures/phase-breakdown.svg)

# Alethe Replay Scaling

Each point is a successful strict Alethe replay, with repeated observations
averaged per VC. The horizontal axis counts parsed certificate commands and
the replay-time axis is logarithmic. The plot shows samples without a fitted
trend; certificate size alone does not determine replay cost.

![Alethe replay time against parsed certificate commands](figures/alethe-replay-scaling.svg)
