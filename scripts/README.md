# Benchmark Scripts

The benchmark harnesses compare lean-auto, Duper, `grind`, and the local
lean-crush build. Crush is measured separately in trusted-verification,
core-reconstruction, Alethe-replay, and portfolio-reconstruction lanes.
Generated sources, logs, metadata, per-VC measurements, and summaries are
written under `BenchmarkResults/`.

| Script | Benchmarks |
|---|---|
| `benchmark-corpora.sh` | LeanHammer, Loom, Cashmere, and Velvet |
| `benchmark-leanhammer.sh` | Standalone LeanHammer profiles |
| `benchmark-plean.sh` | PLean verification conditions |
| `benchmark-common.sh` | Shared pinned-source provisioning |
| `with-local-crush.sh` | Runs a downstream Lean file against the local Crush build |
| `plot-benchmarks.py` | Renders normalized reports as Markdown tables and SVG figures |

The latest recorded results and exact tested revisions are in
[`BENCHMARKS.md`](../BENCHMARKS.md). The machine-readable inputs for the
published 2026-08-20 figures and baseline comparison are retained in
[`BenchmarkResults/recorded/2026-08-20`](../BenchmarkResults/recorded/2026-08-20).

## Prerequisites

Install Git and the Lean toolchain manager, and make Z3 and cvc5 available on
`PATH`:

```sh
git --version
lake --version
z3 --version
cvc5 --version
```

The harnesses build local Crush and every downstream Lake package they use.
They clone pinned source revisions into `BenchmarkResults/sources`, reuse that
cache on later runs, and create detached temporary worktrees. A fresh run
therefore needs network access but no manually prepared sibling repositories.

Set `BENCHMARK_SOURCE_CACHE` to store clones elsewhere. `HAMMER_REPO`,
`LOOM_REPO`, `VELVET_REPO`, `PLEAN_AUTO_TREE`, `PLEAN_DUPER_TREE`, and
`PLEAN_CRUSH_TREE` override automatic provisioning with existing checkouts.
The scripts do not switch their branches, though normal Lake commands may
update build or manifest state.

## Corpus Benchmark

Run all LeanHammer, Loom, Cashmere, and Velvet cases once:

```sh
REPEATS=1 \
TIMEOUT=5 \
DUPER_TIMEOUT=5 \
SOLVER=cvc5 \
CRUSH_MODES=verify \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
OUT_DIR="$PWD/BenchmarkResults/corpora-reproduction" \
scripts/benchmark-corpora.sh
```

`TIMEOUT` is the solver timeout for each query. `MAX_HEARTBEATS` is a separate
Lean budget for each recorded VC. Generated Loom and Velvet files enumerate
their VCs with one worker, record every backend success or failure, and admit
failed goals only inside the temporary benchmark source so one failure cannot
suppress later VCs. The enclosing declaration is uncapped.
`MAX_RECURSION_DEPTH` applies uniformly to every generated Lean process and is
recorded in `metadata.tsv`.

The command runs the four headline backends: Auto, Duper, trusted Crush, and
`grind`. `CRUSH_MODES=verify` selects `crush.trust = "trust"` and does not
perform proof reconstruction. The script writes partial diagnostics but exits
nonzero if a lane is truncated or lacks any VC from the fixed workload.

For performance measurements, use multiple repeats:

```sh
REPEATS=3 CRUSH_MODES=verify MAX_HEARTBEATS=0 \
  scripts/benchmark-corpora.sh
```

Select corpora or backends with `RUN_*` variables:

```sh
RUN_LEANHAMMER=false \
RUN_LOOM=false \
RUN_CASHMERE=false \
scripts/benchmark-corpora.sh

RUN_AUTO=false scripts/benchmark-corpora.sh
RUN_CRUSH=false scripts/benchmark-corpora.sh
RUN_DUPER=false scripts/benchmark-corpora.sh
RUN_GRIND=false scripts/benchmark-corpora.sh
```

Run selected Cashmere or Velvet files:

```sh
RUN_LEANHAMMER=false \
RUN_LOOM=false \
RUN_CASHMERE=false \
VELVET_CASES="Velvet/Examples/GCD.lean Velvet/Examples/IsSorted.lean" \
scripts/benchmark-corpora.sh
```

Useful overrides include:

| Variable | Default | Purpose |
|---|---|---|
| `HAMMER_REF` | `df4dd136...` | LeanHammer revision |
| `LOOM_AUTO_REF` | `78928abc...` | Loom lean-auto revision |
| `LOOM_CRUSH_REF` | `ec16b95f...` | Loom Crush revision |
| `LOOM_DUPER_REF` | pinned commit | Loom Duper revision |
| `VELVET_AUTO_REF` | `d254391d...` | Velvet lean-auto revision |
| `VELVET_CRUSH_REF` | `e90d7934...` | Velvet Crush revision |
| `VELVET_DUPER_REF` | pinned commit | Velvet Duper revision |
| `BENCHMARK_SOURCE_CACHE` | `BenchmarkResults/sources` | Cached Git repositories |
| `OUT_DIR` | timestamped directory | Result location |
| `DUPER_TIMEOUT` | `5` | Duper saturation limit per portfolio instance |
| `CRUSH_MODES` | `verify core alethe portfolio` | Crush measurement lanes |
| `HAMMER_PROFILES` | derived from enabled backends | Explicit LeanHammer profiles |
| `MAX_RECURSION_DEPTH` | `1000000` | Lean recursion limit for generated files |
| `USE_MATHLIB_CACHE` | `true` | Fetch Mathlib build artifacts |
| `CRUSH_PROFILE` | `true` | Include Crush phase profiling and report records |
| `KEEP_WORKTREES` | `false` | Retain temporary detached worktrees |

## LeanHammer

The standalone harness defaults to the published Z3-based `crush-only` lane,
direct cvc5 verification and reconstruction lanes, `grind-only`,
`duper-only`, LeanHammer's Auto/Duper lanes, and `aesop-crush`:

```sh
REPEATS=3 \
scripts/benchmark-leanhammer.sh
```

The harness provisions and builds its pinned LeanHammer revision. The
import-only case is recorded but excluded from its summary.
`duper-only` invokes raw `duper [*]`. `auto-duper` is LeanHammer's pipeline
where Lean-auto preprocessing and monomorphization feed Duper; it is not a
sequential `auto`-then-Duper fallback. Set `PROFILES` to run selected lanes.

## PLean

Run all four PLean headline lanes:

```sh
RUN_DUPER=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
CRUSH_MODES=verify \
MAX_HEARTBEATS=1000000 \
CRUSH_INST_FUEL=0 \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=0 \
OUT_DIR="$PWD/BenchmarkResults/plean-reproduction" \
scripts/benchmark-plean.sh
```

The defaults provision `AD1024/P` at `be397267...` for auto and
`9c098b4c...` for Crush. The auto revision is the benchmarked child of
`p-org/P`'s `dev/p-lean` revision `887f189d...`; the Crush revision commits the
exact adaptation previously identified by tracked diff
`ba75ebbc5de1586515b87c1e2eae23765078422e141d62f2488073dcf3e9d33b`.
Override the corresponding `PLEAN_*_REPO_URL`, `PLEAN_*_REV`, or
`PLEAN_*_TREE` variable to test other published revisions.

`MAX_HEARTBEATS` defaults to `1000000` for auto and Crush.
The PLean Duper lane uses `DUPER_TIMEOUT=1` and
`DUPER_MAX_HEARTBEATS=20000`. `DUPER_FILE_CPU_SECONDS=0` leaves the file
uncapped so every obligation receives an attempt. A positive value is useful
for bounded diagnostics, but a capped file may leave VCs `missing`; such a run
cannot produce a valid all-VC headline comparison and exits nonzero after
writing its reports.
Set `PREPARE_TREES=false` only when all selected override trees and their
dependencies are already built.

The Duper lane is opt-in because it is substantially slower than the other
lanes. To run only Duper on the full workload:

```sh
RUN_AUTO=false \
RUN_CRUSH=false \
RUN_DUPER=true \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=0 \
REPEATS=1 \
OUT_DIR="$PWD/BenchmarkResults/plean-duper-stress" \
scripts/benchmark-plean.sh
```

The focused command writes only Duper results. Use the all-lanes command above
to generate a fixed-denominator PLean headline table and the pairwise
Crush-versus-baseline rows in `comparison.tsv`.

The PLean harness disables registered manual proofs in temporary generated
sources so every backend receives the same VCs. It excludes incomplete
`Paxos.lean`; override `PLEAN_CASES` to select a space-separated file list.

## Outputs

All harnesses write normalized measurement, profiling, coverage, and comparison
reports:

| File | Contents |
|---|---|
| `metadata.tsv` | Revisions, toolchains, solver configuration, and dirty state |
| `results.tsv` | Per-VC status, failure category, and tactic-local time |
| `runs.tsv` | Per-file wall time, exit status, and VC count; corpus runs also record truncation |
| `summary.tsv` | Legacy raw-record aggregate emitted by the host harness |
| `headline-summary.tsv` | Auto, Duper, trusted Crush, and `grind` coverage over one fixed all-VC denominator |
| `comparison.tsv` | Pairwise matched-VC outcomes for Crush versus one baseline at a time |
| `file-summary.tsv` | PLean-only per-file coverage and timing |
| `measurements.tsv` | Normalized per-VC status and tactic-local time |
| `profile-events.tsv` | Normalized Crush outcomes, replay failures, phases, and numeric metrics |
| `coverage-summary.tsv` | All-lane coverage over a fixed suite denominator, including attempted, failed, and missing counts |
| `reconstruction-summary.tsv` | Verified VCs reconstructed by Core, Alethe, and the portfolio |
| `reconstruction-failures.tsv` | Reconstruction failures grouped by reported cause |
| `outcome-summary.tsv` | Crush outcomes and replay statuses grouped by suite and lane |
| `phase-summary.tsv` | Total, mean, minimum, and maximum time for each Crush phase |
| `alethe-replay-scaling.tsv` | Successful Alethe replays with certificate size and replay time |
| `alethe-replay-scaling-summary.tsv` | Correlation and least-squares scaling grouped by suite and lane |
| `logs/` | Complete Lean and solver output |

`alethe-replay-scaling.tsv` uses the number of parsed Alethe commands as its
primary script-length measure. It also records parsed S-expression nodes and
the byte length of the certificate's canonical S-expression rendering.
`replay_nanos` covers parsing, replay, proof assembly, and final kernel
checking, but excludes solver time. The summary reports Pearson correlation,
R-squared, milliseconds per 100 commands, and milliseconds per KiB only when
at least two successful VCs have nonzero size and time variance. Repeated runs
are preserved in the detailed file and averaged per VC before fitting, so they
do not over-weight one obligation.

In `headline-summary.tsv`, `total_vcs` is the fixed number of VC occurrences in
the corpus and is identical for every backend. `attempted_vcs` counts VCs with
a complete backend record. `failed_vcs` counts attempted but unsolved VCs.
`missing_vcs` counts corpus VCs for which the backend produced no complete
attempt record; missing VCs count as unsolved in `pass_pct` and are excluded
from timing statistics.

In `comparison.tsv`, `matched_vcs` is the exact VC-identity intersection for
the named baseline and Crush. `baseline_only_solved`, `crush_only_solved`,
`both_solved`, and `neither_solved` partition that intersection. The two timing
means include only `both_solved` VCs. There are no baseline-versus-baseline
rows.

## Tables and Figures

Render one or more completed result directories with only the Python standard
library:

```sh
python3 scripts/plot-benchmarks.py \
  BenchmarkResults/corpora-reproduction \
  BenchmarkResults/leanhammer-reproduction \
  BenchmarkResults/plean-reproduction \
  --out-dir BenchmarkResults/figures
```

Each input must contain the normalized TSV reports listed above. Use only one
input for a given corpus and lane; the script rejects conflicting aggregate
rows rather than silently combining different runs. Exact duplicate rows are
ignored.

The command writes:

| File | Contents |
|---|---|
| `tables.md` | All-VC backend comparison, pairwise matched-VC, reconstruction, failure, phase, and scaling tables |
| `coverage.svg` | Solved VCs by corpus and lane |
| `reconstruction.svg` | Core, Alethe, and portfolio reconstruction among verified VCs |
| `reconstruction-failures.svg` | One failure-mode pie chart per corpus |
| `phase-breakdown.svg` | Stacked profiler-accounted time by Crush phase |
| `alethe-replay-scaling.svg` | Successful replay time against parsed command count |

The scaling plot defaults to a logarithmic replay-time axis because measured
replays span several orders of magnitude. Pass `--replay-axis linear` for a
linear axis. In either view, the annotation and dashed line report the
least-squares fit in the original linear units.

The Verso manual publishes a checked-in snapshot of the SVGs. Reproduce that
exact snapshot from the retained result directories:

```sh
python3 scripts/plot-benchmarks.py \
  BenchmarkResults/recorded/2026-08-20/figures/corpora \
  BenchmarkResults/recorded/2026-08-20/figures/leanhammer \
  BenchmarkResults/recorded/2026-08-20/figures/plean \
  --out-dir Doc/Verso/figures \
  --skip-tables
```

Use `headline-summary.tsv` for all-VC coverage. Use `comparison.tsv` only for
pairwise analysis of exact VCs shared by Crush and one baseline.
