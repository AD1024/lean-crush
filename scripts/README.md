# Benchmark Scripts

The benchmark harnesses compare lean-auto, Duper, `grind`, and the local
lean-crush build. The headline comparison uses trusted Crush
(`crush.trust = "trust"`); Core, Alethe, and portfolio reconstruction are
measured separately. Generated sources, logs, metadata, per-VC measurements,
and summaries are written under `BenchmarkResults/`.

| Script | Benchmarks |
|---|---|
| `../benchmark.sh` | Published headline run selected by case study and backend |
| `../benchmark-crush-modes.sh` | Trusted and reconstructed Crush modes |
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

For the standard one-repeat reproduction, select one case study (or all four)
and one backend:

```sh
bash benchmark.sh \
  --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
  --with <crush|auto|duper|grind>
```

The wrapper uses the published revisions and resource settings, fetches Lake
cache artifacts when available, and writes normalized reports and plots under
`BenchmarkResults/reproduction-<timestamp>-<backend>`.

Resume an interrupted wrapper run in the same directory, using the same
case-study and backend selection:

```sh
bash benchmark.sh \
  --case_study all \
  --with crush \
  --resume BenchmarkResults/reproduction-<timestamp>-crush
```

Regenerate only the headline figures and tables from an existing wrapper run:

```sh
bash benchmark.sh --plot_only BenchmarkResults/reproduction-<timestamp>-<backend>
```

Run the four Crush verification and reconstruction modes for one case study,
or for all four:

```sh
bash benchmark-crush-modes.sh \
  --case_study <all|LeanHammer|Velvet|Cashmere|PLean>
```

This writes the reconstruction, failure, phase-breakdown, and Alethe replay
comparison under `BenchmarkResults/crush-modes-<timestamp>`.

Resume an interrupted mode study in place with:

```sh
bash benchmark-crush-modes.sh \
  --case_study all \
  --resume BenchmarkResults/crush-modes-<timestamp>
```

Both wrappers propagate `RESUME=true` to their selected harnesses. Each
harness records a checkpoint only after a complete case/profile/repeat has
flushed its result, measurement, and profiling records. On resume, completed
units are skipped and incomplete or truncated units have their partial rows
removed before they are rerun. Result directories made by older versions of
the scripts are bootstrapped from their completed aggregate rows. Keep all
selectors, revisions, and resource settings unchanged when resuming a run.
The harness still prepares and checks the pinned downstream trees before it
dispatches the remaining benchmark units.

Regenerate only those comparison artifacts with:

```sh
bash benchmark-crush-modes.sh \
  --plot_only BenchmarkResults/crush-modes-<timestamp>
```

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
recorded in `metadata.tsv`. Generated Lean processes disable asynchronous
elaboration so tactic-local measurements do not overlap.

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
| `CRUSH_TRACE_REPLAY` | `false` | Emit rule-, method-, and phase-level Alethe replay telemetry |
| `KEEP_WORKTREES` | `false` | Retain temporary detached worktrees |
| `RESUME` | `false` | Reuse completed checkpoints in an existing `OUT_DIR` |

The corpus, standalone LeanHammer, and PLean harnesses fetch cached build
artifacts by default. They try native `lake cache get` first and retain the
Mathlib cache executable as a compatibility fallback for older pinned Lake
versions. Set `USE_MATHLIB_CACHE=false` to force a source build.

To resume any harness directly, repeat its original command with the same
settings and add `RESUME=true`, preserving its original `OUT_DIR`:

```sh
RESUME=true \
OUT_DIR="$PWD/BenchmarkResults/corpora-reproduction" \
scripts/benchmark-corpora.sh
```

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
writing its reports. The harness also rejects errors in its generated benchmark
prelude even when Lean recovers and emits later VC records.
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
| `checkpoints.tsv` | Fully recorded benchmark work units used by `RESUME=true` |
| `metadata.tsv` | Revisions, toolchains, solver configuration, and dirty state |
| `results.tsv` | Per-VC status, failure category, and tactic-local time |
| `runs.tsv` | Per-file wall time, exit status, and VC count; corpus runs also record truncation |
| `summary.tsv` | Legacy raw-record aggregate emitted by the host harness |
| `headline-summary.tsv` | Auto, Duper, trusted Crush, and `grind` coverage over one fixed all-VC denominator |
| `headline-outcomes.tsv` | Headline VCs partitioned into success, translation error, timeout, and failed to prove |
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

In `headline-outcomes.tsv`, the four outcome counts sum to `total_vcs`.
`translation_error` requires an explicit unsupported translation or encoding
diagnostic. `timeout` requires an explicit wall-clock, heartbeat, or saturation
limit. `failed_to_prove` contains every other unsuccessful attempt, including
solver `sat` or `unknown`, exhausted proof search, and ordinary tactic errors.
The report rejects nonuniform headline workloads rather than adding a fifth
`missing` outcome.

### Error and failure categories

The per-attempt `category` in `results.tsv` and `measurements.tsv` describes the
diagnostic emitted by the benchmarked tactic. The shell harnesses classify it
as follows:

| Category | Diagnostic that selects it |
|---|---|
| `-` | The tactic closed the VC. |
| `timeout` | A solver timeout, Lean heartbeat exhaustion, or Duper saturation-time/limit diagnostic. |
| `translation` | Text reporting an unsupported translation or encoding, higher-order input, or an inability to translate or encode a term. |
| `unknown` | The corpus harness received another solver `unknown` diagnostic. LeanHammer and PLean fold this into `tactic`. |
| `sat` | The corpus harness was told that the goal was not provable or false, normally because the solver found a model. LeanHammer and PLean fold this into `tactic`. |
| `reconstruction` | The corpus harness received an Alethe or other reconstruction diagnostic that did not match an earlier category. |
| `tactic` | No more specific rule matched; this includes ordinary proof-search failures and harness-specific diagnostics that expose no finer reason. |

Timeout matching has priority over translation in the shell harnesses. The
corpus harness then checks `unknown`, `sat`, and reconstruction in that order.
LeanHammer and PLean expose only `timeout`, `translation`, and the `tactic`
fallback at this layer.

`headline-outcomes.tsv` deliberately uses a smaller, backend-independent
taxonomy. An all-pass VC is `success`. Otherwise an explicit translation or
unsupported-encoding marker gives `translation_error`; if none exists, an
explicit timeout, heartbeat, or saturation-limit marker gives `timeout`.
Everything else is `failed_to_prove`. Thus solver `sat` and `unknown` remain
distinguishable in the raw/profile data but are both `failed_to_prove` in the
headline outcome partition.

`reconstruction-failures.tsv` has a separate taxonomy for VCs that trusted
`crush-verify` solved but a checked reconstruction lane did not:

| Failure mode | Meaning |
|---|---|
| `certificate-error` | cvc5 returned an explicit `(error "...")` in its proof output instead of a usable Alethe certificate. For example, cvc5 may report `Proof unsupported by Alethe: contains operator DUMMY_SKOLEM`. This is a certificate-generation limitation, not a Lean kernel rejection. |
| `no-certificate` | The solver returned no Alethe proof output. |
| `malformed-certificate` | Proof output was nonempty but had no parseable command list, or the parsed proof was structurally unusable, such as a missing referenced premise or empty-clause conclusion. |
| `term-gap` | A certificate assumption, clause, sort, operator, or anchor term could not be decoded into the corresponding Lean proposition or binder. |
| `rule-gap` | The certificate step was decoded, but Lean could not prove that concrete inference from its already replayed premises. It also covers a decoded SMT assumption that cannot be derived from its Lean source fact. |
| `kernel-reject` | Replay constructed a candidate final proof, but the final elaborator/kernel check rejected it. |
| `replay-exception` | An unexpected exception escaped while replaying the certificate. |
| `core-failed` | The core reconstruction lane received `unsat`, but none of its checked finishing tactics closed the goal from the selected unsat-core facts and explicit reconstruction hints. |
| `<replay-mode>+core-failed` | In the portfolio lane, Alethe replay failed for `<replay-mode>` and the core-directed fallback failed too; for example, `certificate-error+core-failed`. |
| `solver-sat` | The reconstruction lane's solver returned `sat`. |
| `solver-unknown` | The reconstruction lane's solver returned `unknown`, including solver timeouts represented by an `unknown` profile event. |
| `not-attempted` | No attempt row was available for that verified VC and reconstruction lane. |
| `tactic` / `unclassified` | No more specific profiler failure was available, so the report used the per-attempt category or the final fallback. |

For strict Alethe, a `reconstruction-failed` profiler event maps directly to
its replay label. For Core it maps to `core-failed`. For the portfolio, the
replay label is combined with `core-failed` because both reconstruction paths
must have failed. If multiple profiler events exist for one VC, the report uses
the most frequently occurring candidate category.

The exact diagnostic is retained with different fidelity by each harness.
Corpus `results.tsv` and `measurements.tsv` contain the complete diagnostic
with tabs and newlines flattened. LeanHammer `measurements.tsv` retains the
first matching diagnostic or error line. PLean's normalized attempt rows retain
only the coarse category, while `profile-events.tsv` contains the structured
replay label and concise detail. The complete original Lean and solver output
is always in the corresponding file under `logs/`.

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
ignored. Repeat `--only` to select outputs, for example
`--only tables --only coverage`.

The command writes:

| File | Contents |
|---|---|
| `tables.md` | All-VC backend comparison, pairwise matched-VC, reconstruction, failure, phase, and scaling tables |
| `coverage.svg` | Solved VCs by corpus and headline backend |
| `outcomes.svg` | Four-way stacked outcome partition for every corpus and headline backend |
| `reconstruction.svg` | Core, Alethe, and portfolio reconstruction among verified VCs |
| `reconstruction-failures.svg` | One failure-mode pie chart per corpus |
| `phase-breakdown.svg` | Stacked profiler-accounted time by Crush phase |
| `alethe-replay-scaling.svg` | Successful replay time against parsed command count |

The scaling plot defaults to a logarithmic replay-time axis because measured
replays span several orders of magnitude. Pass `--replay-axis linear` for a
linear axis. In either view, the annotation and dashed line report the
least-squares fit in the original linear units.

The canonical inputs for every published table and figure are under
[`scripts/benchmark-data`](benchmark-data).
Regenerate all artifacts into `BenchmarkResults/figures` with:

```sh
scripts/render-paper-artifacts.sh
```

Pass a different output directory as the first argument:

```sh
scripts/render-paper-artifacts.sh /tmp/lean-crush-paper-artifacts
```

The renderer reads `benchmark-data/main` for the all-backend comparison and
`benchmark-data/crush-modes` for reconstruction, failure, phase, and replay-scaling
measurements. Their workloads are intentionally separate because the
reconstruction study predates the latest expanded Velvet workload. The
[benchmark-data README](benchmark-data/README.md)
lists the direct `plot-benchmarks.py` inputs.

## Paper Artifacts

Run these commands from the repository root. They use the pinned revisions
documented above and write to fresh result directories under
`BenchmarkResults/`. The published snapshot uses one repeat; use
`REPEATS=3` or more when drawing performance conclusions from a new machine.
Choose unused `MAIN_ROOT` and `DETAIL_ROOT` paths for each measurement so
results and logs from separate runs remain distinguishable.

### 1. Main Comparison

This run gives every backend the same fixed VC set. Its Crush lane sets
`crush.trust = "trust"` through `CRUSH_MODES=verify`.

```sh
MAIN_ROOT="$PWD/BenchmarkResults/paper-main"

RUN_LEANHAMMER=false \
RUN_LOOM=true \
RUN_CASHMERE=true \
RUN_VELVET=true \
RUN_AUTO=true \
RUN_DUPER=true \
RUN_CRUSH=true \
RUN_GRIND=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
DUPER_TIMEOUT=5 \
CRUSH_MODES=verify \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$MAIN_ROOT/corpora" \
scripts/benchmark-corpora.sh

PROFILES="auto-duper duper-only crush-verify grind-only" \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
DUPER_TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$MAIN_ROOT/leanhammer" \
scripts/benchmark-leanhammer.sh

RUN_AUTO=true \
RUN_DUPER=true \
RUN_CRUSH=true \
RUN_GRIND=true \
PREPARE_TREES=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
CRUSH_MODES=verify \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_INST_FUEL=0 \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=0 \
GRIND_SPLITS=20 \
CRUSH_PROFILE=true \
OUT_DIR="$MAIN_ROOT/plean" \
scripts/benchmark-plean.sh

python3 scripts/plot-benchmarks.py \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$MAIN_ROOT/artifacts" \
  --only tables \
  --only coverage
```

The main all-VC table is `artifacts/tables.md` under **Backend Comparison**.
`artifacts/coverage.svg` is its coverage figure. Every headline lane must have
zero `missing_vcs`; each harness exits nonzero otherwise.

### 2. Aligned VC Comparisons

The main run already writes exact per-VC identities. Render its pairwise
Crush-versus-baseline joins without rerunning a solver:

```sh
MAIN_ROOT="$PWD/BenchmarkResults/paper-main"

python3 scripts/plot-benchmarks.py \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$MAIN_ROOT/aligned" \
  --only tables
```

Use **Pairwise Matched VCs** in `aligned/tables.md`, or the `comparison.tsv`
file in each input directory. Each row compares trusted Crush with one
baseline on their exact VC-identity intersection; it does not compare two
baselines or substitute equal-sized workloads for identity matching.

### 3. Outcome Charts

Generate the stacked success, translation-error, timeout, and
failed-to-prove chart from the same fixed-workload main run:

```sh
MAIN_ROOT="$PWD/BenchmarkResults/paper-main"

python3 scripts/plot-benchmarks.py \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$MAIN_ROOT/outcomes" \
  --only outcomes
```

The result is `outcomes/outcomes.svg`. Every bar partitions its corpus total;
the plotter rejects missing attempts, inconsistent totals, and incomplete
four-way partitions.

### 4. Detailed Crush Measurements

Run trusted verification, Core reconstruction, strict Alethe replay, and the
reconstruction portfolio without rerunning baseline backends. These lanes vary
`crush.trust` and `crush.reconstruct`; all other listed solver and resource
options remain fixed.

```sh
DETAIL_ROOT="$PWD/BenchmarkResults/paper-crush-modes"

RUN_LEANHAMMER=false \
RUN_LOOM=true \
RUN_CASHMERE=true \
RUN_VELVET=true \
RUN_AUTO=false \
RUN_DUPER=false \
RUN_CRUSH=true \
RUN_GRIND=false \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
CRUSH_MODES="verify core alethe portfolio" \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$DETAIL_ROOT/corpora" \
scripts/benchmark-corpora.sh

PROFILES="crush-verify crush-core crush-alethe crush-portfolio" \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$DETAIL_ROOT/leanhammer" \
scripts/benchmark-leanhammer.sh

RUN_AUTO=false \
RUN_DUPER=false \
RUN_CRUSH=true \
RUN_GRIND=false \
PREPARE_TREES=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
CRUSH_MODES="verify core alethe portfolio" \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_INST_FUEL=0 \
CRUSH_PROFILE=true \
OUT_DIR="$DETAIL_ROOT/plean" \
scripts/benchmark-plean.sh

python3 scripts/plot-benchmarks.py \
  "$DETAIL_ROOT/corpora" \
  "$DETAIL_ROOT/leanhammer" \
  "$DETAIL_ROOT/plean" \
  --out-dir "$DETAIL_ROOT/artifacts" \
  --only tables \
  --only reconstruction \
  --only reconstruction-failures \
  --only phase-breakdown \
  --only alethe-replay-scaling
```

The generated tables report mode coverage, reconstruction failures, profiler
phase timing, and Alethe replay scaling. The SVGs visualize the corresponding
reconstruction coverage, failure distribution, phase shares, and replay-time
scaling.
