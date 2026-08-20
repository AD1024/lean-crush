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
gives self-contained reproduction commands.

# Verification Coverage

The verification figure counts a VC as solved when the selected lane closes
the generated Lean goal. `Crush verify` uses trusted SMT discharge and measures
whether collection, specialization, translation, and solving succeed.
`Core`, `Alethe`, and `Portfolio` additionally require a kernel-checked proof.
`grind` is run on the same generated obligations as a Lean baseline.

![Verification coverage by corpus and lane](../../figures/coverage.svg)

# Proof Reconstruction

The reconstruction denominator is the set of VCs discharged by the trusted
verification lane. Core reconstruction re-proves an unsat core with Lean
tactics. Alethe reconstruction replays cvc5's refutation step by step. The
portfolio first attempts Alethe and then falls back to core reconstruction.

![Checked proof reconstruction among SMT-verified VCs](../../figures/reconstruction.svg)

Failure modes distinguish missing or malformed certificates, unsupported
Alethe rules or terms, solver `sat` and `unknown` results, and failures of
core-directed Lean reconstruction. `not-attempted` means an earlier failure or
declaration heartbeat stopped the generated file before that VC reached the
strict lane; it is not classified as a reconstruction attempt.

![Proof reconstruction failures grouped by reported cause](../../figures/reconstruction-failures.svg)

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
