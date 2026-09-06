# Benchmark Scripts

The benchmark harnesses compare lean-auto, Duper, `grind`,
[lean-smt](https://github.com/ufmg-smite/lean-smt), and the local lean-crush
build. The headline comparison uses trusted Crush (`crush.trust = "trust"`);
Core, Alethe, and portfolio reconstruction are measured separately. Generated
sources, logs, metadata, per-VC measurements, and summaries are written under
`BenchmarkResults/`.

| Script | Benchmarks |
|---|---|
| `../benchmark.sh` | Published headline run selected by case study and backend |
| `../benchmark-crush-modes.sh` | Trusted and reconstructed Crush modes |
| `../benchmark-reconstruction.sh` | lean-smt against Crush's Alethe and portfolio reconstruction |
| `benchmark-corpora.sh` | LeanHammer, Loom, Cashmere, and Velvet |
| `benchmark-leanhammer.sh` | Standalone LeanHammer profiles |
| `benchmark-plean.sh` | PLean verification conditions |
| `benchmark-common.sh` | Shared pinned-source provisioning |
| `with-local-crush.sh` | Runs a downstream Lean file against the local Crush build |
| `plot-benchmarks.py` | Renders normalized reports as Markdown tables and SVG figures |
| `plot-time-coverage.py` | Renders time-versus-coverage curves with matplotlib |
| `patches/` | Recorded backend patches applied to pinned corpus revisions |

The latest recorded results and exact tested revisions are in
[`BENCHMARKS.md`](../BENCHMARKS.md). The machine-readable inputs for the
published 2026-08-20 figures and baseline comparison are retained in
[`BenchmarkResults/recorded/2026-08-20`](../BenchmarkResults/recorded/2026-08-20).

For the standard one-repeat reproduction, select one case study (or all four)
and one backend:

```sh
bash benchmark.sh \
  --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
  --with <crush|auto|duper|grind|lean-smt>
```

The wrapper uses the published revisions and resource settings, fetches Lake
cache artifacts when available, and writes normalized reports and plots under
`BenchmarkResults/reproduction-<timestamp>-<backend>`.

lean-smt is a fifth headline backend, restricted to LeanHammer:

```sh
bash benchmark.sh --case_study LeanHammer --with lean-smt
```

Only the pinned LeanHammer tree requires lean-smt, so `--with lean-smt`
rejects any other case study rather than silently measuring nothing. See
[lean-smt](#lean-smt) for why the other corpora are not provisioned.

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

Compare checked proof reconstruction between lean-smt, Crush's strict Alethe
replay, and Crush's reconstruction portfolio:

```sh
bash benchmark-reconstruction.sh --case_study LeanHammer
```

This runs the `crush-verify`, `crush-alethe`, `crush-portfolio`, and
`smt-only` lanes on one workload and writes the reconstruction comparison,
its failure breakdown, and the Alethe replay scaling under
`BenchmarkResults/reconstruction-<timestamp>`. It accepts the same `--resume`
and `--plot_only` arguments as the other two wrappers.

## Prerequisites

Install Git and the Lean toolchain manager, and make Z3 and cvc5 available on
`PATH`:

```sh
git --version
lake --version
z3 --version
cvc5 --version
```

The lean-smt lane is the one exception: it calls cvc5 through the in-process
`lean-cvc5` bindings that its Lake package links, so it uses neither the `cvc5`
executable on `PATH` nor `CVC5_BIN`. Its lane records the resolved lean-smt
commit in `metadata.tsv`, and it refuses to run under `SOLVER=z3` rather than
reporting cvc5 results under a Z3 label.

`plot-benchmarks.py` and `benchmark-report.py` use only the Python standard
library. `plot-time-coverage.py` is the one script that needs a third-party
package:

```sh
python3 -m pip install matplotlib
```

No harness or wrapper invokes it, so the reproduction commands above run
without matplotlib installed.

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

`RUN_SMT=true` adds the lean-smt lane. It applies only to the LeanHammer
sub-suite, so it requires `RUN_LEANHAMMER=true` and `SOLVER=cvc5`:

```sh
RUN_SMT=true RUN_LEANHAMMER=true scripts/benchmark-corpora.sh
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
| `LOOM_SMT_REF` | `LOOM_CRUSH_REF` | Loom revision the lean-smt lane patches |
| `VELVET_SMT_REF` | `VELVET_CRUSH_REF` | Velvet revision the lean-smt lane patches |
| `RUN_SMT` | `false` | Add the lean-smt lane |
| `SMT_REPO_URL` | `ufmg-smite/lean-smt.git` | lean-smt remote |
| `SMT_REV` | `e5025665...` | lean-smt revision (`no_mathlib`) |
| `SMT_TIMEOUT` | `TIMEOUT` | lean-smt solver timeout per query |
| `SMT_MONO` | `true` | Pass `+mono` so lean-smt monomorphizes first |
| `SMT_TREE_ROOT` | unset | Directory that keeps the lean-smt trees between runs |
| `HAMMER_PROFILES` | derived from enabled backends | Explicit LeanHammer profiles |
| `MAX_RECURSION_DEPTH` | `1000000` | Lean recursion limit for generated files |
| `USE_MATHLIB_CACHE` | `true` | Fetch Mathlib build artifacts |
| `BENCHMARK_CACHE_TIMEOUT` | `1200` | Seconds before a stalled cache fetch fails over (`0` disables) |
| `CRUSH_PROFILE` | `true` | Include Crush phase profiling and report records |
| `CRUSH_TRACE_REPLAY` | `false` | Emit rule-, method-, and phase-level Alethe replay telemetry |
| `KEEP_WORKTREES` | `false` | Retain temporary detached worktrees |
| `RESUME` | `false` | Reuse completed checkpoints in an existing `OUT_DIR` |

Lake fetches build outputs with `curl --retry 3` and no `--max-time`, and
`--retry` only retries a request that *fails* — a connection that goes quiet
without closing blocks forever, which looks exactly like a slow build.
`BENCHMARK_CACHE_TIMEOUT` bounds each cache attempt so a hung request falls
through to the next strategy (legacy `cache get`, then Mathlib directly, then
building from source) instead of hanging the run.

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
direct cvc5 verification and reconstruction lanes, `smt-only`, `grind-only`,
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

## lean-smt

The `smt-only` lane invokes lean-smt as
`smt +mono (timeout := SMT_TIMEOUT) [*, <case hints>]` on the same goals and
hints every other lane receives. Set `SMT_MONO=false` to drop `+mono`.

Two details of that invocation are forced by lean-smt rather than chosen.
`[*]` already contributes every local hypothesis, so a hint that merely names
one would make Auto's monomorphization reject the entire query with `Auto does
not accept duplicated input terms`; the generated lane therefore drops hints
that are identifiers resolving to a local hypothesis and keeps the rest, which
is how LeanHammer's own `smt` pipeline filters its suggestions. And lean-cvc5
sets `precompileModules`, so `smt` reaches cvc5 through FFI inside the Lean
process instead of spawning a binary: the lane passes
`--load-dynlib=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib`, and
the harness resolves that path after the build and exits if it is missing.
Without it the extern fails only when the tactic first calls it, which would
otherwise look like a proof failure on every VC.

The lane also does not receive `-Dduper.maxSaturationTime`. Its generated file
imports `Smt` alone, and Lean rejects a `-D` for an option that no imported
module declares. The harness now aborts on `invalid -D parameter` rather than
recording a lane that failed every VC for a configuration reason.

### Provisioning The Lane

Only the pinned LeanHammer revision already requires lean-smt, so that lane
reuses LeanHammer's resolved dependency. Loom, Velvet, and PLean predate it,
and each gets it from a recorded patch under [`patches`](patches) applied to a
checkout of the same pinned revision the run measures:

| Patch | Applied to | Adds |
|---|---|---|
| `loom-smt.patch.in` | Loom at `LOOM_SMT_REF` (Cashmere) | `require Smt` |
| `velvet-smt.patch.in` | Velvet at `VELVET_SMT_REF` | `require Smt` |
| `plean-smt.patch.in` | PLean at `PLEAN_SMT_REV` | `require Smt`, `import Smt`, and the backend substitution |

`@SMT_REPO_URL@`, `@SMT_REV@`, and `@SMT_CONFIG@` are substituted before the
patch is applied, exactly as `@GRIND_SPLITS@` is for `plean-grind.patch.in`, so
the recorded configuration and the measured configuration cannot drift apart.
Each harness then re-checks the applied result: the corpora harness greps for
the pinned require, and the PLean harness asserts all three backend sites moved
and that no direct Crush call survives.

`SMT_REV` is lean-smt's `no_mathlib` branch, the revision LeanHammer's own
manifest pins, so all four corpora measure one lean-smt. Its `main` branch
requires Mathlib v4.33.0 and toolchain v4.33.0, while every corpus here pins
Mathlib v4.32.2, so `main` cannot be used without moving each corpus off the
closure the other lanes measure. `no_mathlib` shares main's source and requires
only `auto`, `cvc5`, and `quote4`, all of which resolve to revisions the
corpora already pin.

After patching, the harness runs `lake update Smt`, which resolves the new
require by name. It then diffs the manifest against the pre-update copy and
aborts if any revision the corpus already pinned moved, naming the package that
moved. Measuring a lean-smt lane against a re-resolved Mathlib would make it
incomparable to the lanes it is being compared against, so this is checked
rather than assumed.

PLean reaches its backend from inside `PLean/Verify/Tactic.lean`, so its patch
substitutes the backend there — the same mechanism the `grind` lane uses — and
trims `pverify`'s close-chain to the patched path. Both lanes remove the same
four fallbacks (`pverify_structural_smt`, `pverify_split_ite_smt`,
`pverify_split_smt`, `pverify_grind`); leaving them in would credit lean-smt
with obligations another backend closed. `scripts/test_benchmark_patches.py`
pins that the two patches trim the same set.

A lean-smt tree carries its corpus's Mathlib build plus lean-smt's — about 8 GB
for Loom or Velvet — so `SMT_TREE_ROOT` (`--smt_trees`) names a directory that
keeps them between runs. Each tree is created from the pinned revision on first
use and reused afterwards; a reused tree is validated rather than re-patched.
Without it the trees are temporary checkouts, rebuilt every run.

Solver time is native in every lane: the Crush lanes spawn the `cvc5` binary
and lean-smt calls the in-process library. Lean-level code is interpreted in
all lanes, since no lane passes `--load-dynlib` for its own precompiled Lean
modules, so the comparison is not skewed by one lane running compiled while
another is interpreted.

lean-smt reports an Alethe rule it cannot replay by leaving that step as an
open goal rather than by failing, so the generated lane checks the goal list
itself and counts a VC as solved only when no goal remains. Those VCs are
recorded as `rule-gap`. The lane emits one `SMT_PROFILE` record per VC using
the same field layout and reconstruction vocabulary as Crush's
`CRUSH_PROFILE` record, so both tools normalize into the same reports. It
reports no phase timings, because solve and replay time are not separable
from outside the tactic.

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
| `reconstruction-summary.tsv` | Verify-lane successes, the SMT-`unsat` reconstruction cohort, and checked reconstruction coverage |
| `reconstruction-failures.tsv` | Reconstruction failures grouped by reported cause |
| `reconstruction-comparison.tsv` | Checked-proof coverage for lean-smt, Alethe, and portfolio over one matched VC set |
| `reconstruction-comparison-failures.tsv` | Comparison-cohort failures grouped by lane and reported cause |
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
| `reconstruction-failed` | The lean-smt lane returned a diagnostic or left an open goal after replay. |
| `translation-failed` | The lean-smt lane could not encode the goal or a hypothesis into SMT-LIB. |
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

`reconstruction-summary.tsv` distinguishes all VCs closed by `crush-verify`
from the reconstruction cohort. `verify_solved_vcs` counts every successful
verify-lane attempt, including selected facts and checked pre-SMT closures.
`smt_verified_vcs` is the subset whose verify-lane profiler emitted at least
one `outcome=verified`, establishing that the SMT solver actually returned
`unsat`. Only this latter set is used as the denominator for Core, Alethe, and
portfolio reconstruction. This prevents a strict Alethe run from being called
a reconstruction failure merely because it forced a sound-but-incomplete SMT
encoding for a goal that the verify lane had solved before invoking SMT.

`reconstruction-comparison.tsv` compares checked reconstruction across tools,
so it cannot use a Crush-specific denominator. `matched_vcs` is the exact
VC-identity intersection of every compared lane present in the suite, the same
convention `comparison.tsv` uses; a lane is never credited for a VC another
lane did not attempt. The compared lanes are `smt-only`, `crush-alethe`, and
`crush-portfolio`, and a suite needs at least two of them to produce rows.

The table answers two different questions side by side. `checked_proof_vcs`
counts matched VCs the lane closed with a Lean proof term the kernel accepted
by whichever route it took, so a goal that Crush closed by checked pre-SMT
reconstruction counts even though no certificate was replayed. That is the
practical question of whether a tool hands back a checked proof.
`cohort_reconstructed_vcs` asks the narrower certificate question over
`verify_smt_cohort_vcs`, the matched VCs whose trusted Crush lane recorded an
SMT `unsat`, using each lane's own accept set; its `crush-alethe` and
`crush-portfolio` values therefore agree with `reconstruction-summary.tsv`
whenever the matched set covers the whole cohort. The cohort columns are zero
when the run has no `crush-verify` lane.

`common_checked_proof_vcs` counts VCs every compared lane proved.
`common_mean_ms` averages only those VCs, so a lane cannot appear faster by
proving fewer goals; `mean_ms` averages each lane's own successes.

`reconstruction-failures.tsv` has a separate taxonomy for SMT-cohort VCs that
a checked reconstruction lane did not reconstruct:

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
| `not-attempted` | No attempt row was available for that SMT-cohort VC and reconstruction lane. |
| `translation-failed` | lean-smt only. The goal or a hypothesis could not be encoded into SMT-LIB, so the solver was never consulted. |
| `timeout` | lean-smt only. Lean heartbeat exhaustion or a deterministic timeout ended the attempt. |
| `tactic` / `unclassified` | No more specific profiler failure was available, so the report used the per-attempt category or the final fallback. |

For strict Alethe and for lean-smt, a `reconstruction-failed` profiler event
maps directly to its replay label, since neither has a second reconstruction
route. For Core it maps to `core-failed`. For the portfolio, the replay label
is combined with `core-failed` because both reconstruction paths must have
failed. If multiple profiler events exist for one VC, the report uses the most
frequently occurring candidate category.

For lean-smt, `rule-gap` means the certificate was decoded and replayed but at
least one Alethe step had no reconstructor, so lean-smt left it as an open
goal; `term-gap` is a `Failed to reconstruct sort`/`term` diagnostic;
`no-certificate` is `failed to reconstruct proof for unsat result`; and
`certificate-error` is an unexpected `check-sat` verdict. These labels come
from lean-smt's own diagnostics, so they describe its replay layer rather than
Crush's.

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

Repeat `--exclude-suite` to omit a corpus from every table and figure the run
writes. The published artifacts omit Loom, whose four VCs are too few for a
coverage bar or curve to say anything, so the paper reports LeanHammer,
Cashmere, Velvet, and PLean:

```sh
python3 scripts/plot-benchmarks.py \
  BenchmarkResults/corpora-reproduction \
  --out-dir BenchmarkResults/figures \
  --exclude-suite loom
```

`plot-time-coverage.py` takes the same option. The flag only filters what is
rendered; the recorded TSVs keep every suite, and `coverage-summary.tsv` still
reports Loom.

The command writes:

| File | Contents |
|---|---|
| `tables.md` | All-VC backend comparison, pairwise matched-VC, reconstruction, failure, phase, and scaling tables |
| `coverage.svg` | Solved VCs by corpus and headline backend |
| `outcomes.svg` | Four-way stacked outcome partition for every corpus and headline backend |
| `reconstruction.svg` | Core, Alethe, and portfolio VCs closed with a kernel-checked proof, over all VCs |
| `reconstruction-failures.svg` | One failure-mode pie chart per corpus |
| `reconstruction-comparison.svg` | Checked-proof coverage for lean-smt, Alethe, and portfolio |
| `phase-breakdown.svg` | Stacked profiler-accounted time by Crush phase |
| `alethe-replay-scaling.svg` | Successful replay time against parsed command count |

The scaling plot defaults to a logarithmic replay-time axis because measured
replays span several orders of magnitude. Pass `--replay-axis linear` for a
linear axis. In either view, the annotation and dashed line report the
least-squares fit in the original linear units.

### Time Versus Coverage

`plot-time-coverage.py` draws the two comparisons against elapsed time. It is
separate from `plot-benchmarks.py` because it needs matplotlib, and no harness
calls it.

```sh
python3 scripts/plot-time-coverage.py \
  BenchmarkResults/corpora-reproduction \
  BenchmarkResults/leanhammer-reproduction \
  BenchmarkResults/plean-reproduction \
  --out-dir BenchmarkResults/figures
```

| File | Contents |
|---|---|
| `coverage-over-time.svg` | VCs closed against time, one curve per headline backend |
| `coverage-over-time.tsv` | The plotted step positions for that figure |
| `reconstruction-over-time.svg` | VCs reconstructed against time, one curve per compared lane |
| `reconstruction-over-time.tsv` | The plotted step positions for that figure |

The x axis is tactic-local seconds and the y axis counts VCs, closed for the
main comparison and closed with a kernel-checked Lean proof for the
reconstruction comparison. Both figures use one panel per corpus, because
corpora differ by two orders of magnitude in both workload size and time. The
dashed line marks the panel's denominator: the fixed corpus workload for the
main figure, and the matched cohort for the reconstruction figure.

By default a point `(x, y)` reads as "given `x` seconds for each VC, `y` VCs
close", which matches the harnesses giving every VC its own independent
budget. `--mode cumulative` instead puts the running total across VCs on the x
axis, so a point reads as "`y` VCs close within `x` seconds of total tactic
time"; those figures are written with a `-cumulative` suffix so the two do not
overwrite each other.

Repeats of one VC are averaged before the times are sorted, and a VC counts as
solved only when every repeat passed, so the curves use the same conventions
as the tables. Each series therefore ends at exactly the count the tables
report: `solved_vcs` in `headline-summary.tsv` for the main figure, and
`checked_proof_vcs` in `reconstruction-comparison.tsv` for the reconstruction
figure. The script recomputes both and exits nonzero on a mismatch rather than
drawing a curve that disagrees with its table, so it needs each figure's
report alongside `measurements.tsv`.

Useful options:

| Option | Default | Purpose |
|---|---|---|
| `--only main` / `--only reconstruction` | both | Draw one figure; repeat to select several |
| `--exclude-suite SUITE` | none | Omit a corpus; repeat to omit several |
| `--mode per-vc` / `--mode cumulative` | `per-vc` | Per-VC budget or running total on the x axis |
| `--time-axis log` / `--time-axis linear` | `log` | Time axis scale |
| `--format svg` / `pdf` / `png` | `svg` | Figure format |

Measured times are whole milliseconds, so an attempt faster than the
measurement resolution is recorded as `0`. On a logarithmic axis those points
are drawn at 1 ms rather than dropped; `--time-axis linear` places them at 0.

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

`render-paper-artifacts.sh` passes `--exclude-suite loom` and, when
matplotlib is installed, also writes `coverage-over-time.svg`; it warns and
skips that figure otherwise.

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

PROFILES="auto-duper duper-only smt-only crush-verify grind-only" \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
SMT_TIMEOUT=5 \
SMT_MONO=true \
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

python3 scripts/plot-time-coverage.py \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$MAIN_ROOT/artifacts" \
  --only main
```

The main all-VC table is `artifacts/tables.md` under **Backend Comparison**.
`artifacts/coverage.svg` is its coverage figure and
`artifacts/coverage-over-time.svg` plots closed VCs against time. Every headline lane must have
zero `missing_vcs`; each harness exits nonzero otherwise.

The lean-smt row appears only for LeanHammer, because only that tree requires
lean-smt. `validate_uniform_headline` compares VC identities within a corpus,
so a corpus without a lean-smt lane keeps its fixed denominator and the check
still passes. Read the lean-smt row against **Reconstruction Comparison**
rather than against the trusted-Crush row: lean-smt closes a goal only when it
also produces a checked Lean proof, while the `crush-verify` lane trusts the
SMT verdict.

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

### 5. Reconstruction Comparison

Compare lean-smt with Crush's strict Alethe replay and its reconstruction
portfolio on one workload. All three lanes must return a Lean proof term, so
this run answers the checked-reconstruction question that the trusted-Crush
headline lane does not.

```sh
RECONSTRUCT_ROOT="$PWD/BenchmarkResults/paper-reconstruction"

PROFILES="crush-verify crush-alethe crush-portfolio smt-only" \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
SMT_TIMEOUT=5 \
SMT_MONO=true \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$RECONSTRUCT_ROOT/leanhammer" \
scripts/benchmark-leanhammer.sh

python3 scripts/plot-benchmarks.py \
  "$RECONSTRUCT_ROOT/leanhammer" \
  --out-dir "$RECONSTRUCT_ROOT/artifacts" \
  --only tables \
  --only reconstruction \
  --only reconstruction-comparison \
  --only reconstruction-failures \
  --only alethe-replay-scaling

python3 scripts/plot-time-coverage.py \
  "$RECONSTRUCT_ROOT/leanhammer" \
  --out-dir "$RECONSTRUCT_ROOT/artifacts" \
  --only reconstruction
```

`bash benchmark-reconstruction.sh --case_study LeanHammer` runs exactly this
sequence into a timestamped directory. The `crush-verify` lane is included
because it establishes the SMT-`unsat` cohort that the certificate-replay
columns are measured against; it contributes no row to the comparison table
itself.

The other corpora work the same way. Each needs both its lean-smt tree and a
Crush tree — roughly 8 GB each, the Crush one temporary — so with less than
about 25 GB free, run them one at a time and drop each kept tree before the
next, as in [lean-smt Across Every Corpus](#6-lean-smt-across-every-corpus):

```sh
SMT_TREES="$PWD/BenchmarkResults/trees"

for study in Cashmere Velvet PLean; do
  bash benchmark-reconstruction.sh --case_study "$study" \
    --smt_trees "$SMT_TREES" --exclude_suite loom
done
```

Every lane must come from the same run. The recorded
[Detailed Crush Measurements](#4-detailed-crush-measurements) under
`benchmark-data/crush-modes` carry `crush-alethe` and `crush-portfolio` for
every corpus, and since the 2026-09-02 refresh they share every `vc_key` with
the current harness:

| Corpus | crush-modes VCs | current-harness VCs | Shared `vc_key` |
|---|---:|---:|---:|
| LeanHammer | 20 | 20 | 20 |
| PLean | 192 | 192 | 192 |
| Cashmere | 38 | 38 | 38 |
| Velvet | 504 | 504 | 504 |

They still cannot stand in for this comparison's baseline, because they are the
Crush *ablation*: the only lanes present are `crush-verify`, `crush-core`,
`crush-alethe`, and `crush-portfolio`. There is no `smt-only` lane, so a
cross-tool comparison against lean-smt needs a run that measured both.

The snapshot these files replaced keyed VCs by declaration name
(`Cashmere.lean|withdrawSessionExcept_correct|<hash>`) rather than by
occurrence index (`Cashmere.lean|11|<hash>`), which collapsed repeated goals
and shared no `vc_key` with the current harness; its Velvet lanes were also
missing 47 VCs. Neither defect is present in the refreshed data.

Combining the four runs afterwards follows the same rule as the main
comparison — no two directories may supply the same `(suite, lane)` pair:

```sh
RECON="$PWD/BenchmarkResults/reconstruction-all"

python3 scripts/plot-benchmarks.py \
  <leanhammer-run>/leanhammer <cashmere-run>/cashmere \
  <velvet-run>/velvet <plean-run>/plean \
  --out-dir "$RECON/artifacts" --exclude-suite loom \
  --only tables --only reconstruction --only reconstruction-comparison \
  --only reconstruction-failures --only alethe-replay-scaling

python3 scripts/plot-time-coverage.py \
  <leanhammer-run>/leanhammer <cashmere-run>/cashmere \
  <velvet-run>/velvet <plean-run>/plean \
  --out-dir "$RECON/artifacts" --exclude-suite loom --only reconstruction
```

The comparison table is `artifacts/tables.md` under **Reconstruction
Comparison**, its failure breakdown is under **Reconstruction Comparison
Gaps**, `artifacts/reconstruction-comparison.svg` is the corresponding
coverage figure, and `artifacts/reconstruction-over-time.svg` plots
reconstructed VCs against time.

To get the main-comparison lean-smt row and the reconstruction comparison from
one self-consistent run, add the headline lanes to the same invocation. This is
the run recorded in [BENCHMARKS.md](../BENCHMARKS.md#lean-smt):

```sh
SMT_ROOT="$PWD/BenchmarkResults/leanhammer-lean-smt"

PROFILES="auto-duper duper-only smt-only crush-verify crush-core crush-alethe crush-portfolio grind-only" \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
SMT_TIMEOUT=5 \
SMT_MONO=true \
DUPER_TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_PROFILE=true \
OUT_DIR="$SMT_ROOT/leanhammer" \
scripts/benchmark-leanhammer.sh
```

Render its main comparison beside the other corpora, and its reconstruction
comparison on its own. The LeanHammer directory supplies all five headline
backends, so do not also pass a LeanHammer directory from another run: the
plotter rejects the conflicting aggregate rows.

```sh
MAIN_ROOT="$PWD/BenchmarkResults/paper-main"

python3 scripts/plot-benchmarks.py \
  "$SMT_ROOT/leanhammer" \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/plean" \
  --out-dir "$SMT_ROOT/artifacts" \
  --exclude-suite loom \
  --only tables --only coverage --only outcomes

python3 scripts/plot-time-coverage.py \
  "$SMT_ROOT/leanhammer" \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/plean" \
  --out-dir "$SMT_ROOT/artifacts" \
  --exclude-suite loom \
  --only main

python3 scripts/plot-benchmarks.py \
  "$SMT_ROOT/leanhammer" \
  --out-dir "$SMT_ROOT/artifacts/reconstruction" \
  --only tables --only reconstruction --only reconstruction-comparison \
  --only reconstruction-failures --only alethe-replay-scaling

python3 scripts/plot-time-coverage.py \
  "$SMT_ROOT/leanhammer" \
  --out-dir "$SMT_ROOT/artifacts/reconstruction" \
  --only reconstruction
```

### 6. lean-smt Across Every Corpus

The main comparison needs a lean-smt row for LeanHammer, Cashmere, Velvet, and
PLean. Each corpus is a separate run: each needs its own patched tree, and a
tree carries that corpus's Mathlib build plus lean-smt's — about 8 GB. Point
every run at one tree root so the trees are created once and reused, and drop
each one before the next if the disk is tight. From a clean checkout each run
provisions the pinned revision, applies the recorded patch, resolves with
`lake update Smt`, verifies no other pinned revision moved, builds, and
measures.

Validate a corpus on two of its files first — a tree takes most of an hour to
provision, and the subset exercises every step the full run depends on except
the remaining files. `--cases` names files relative to the corpus root and
needs a single `--case_study`, since the names are per corpus:

```sh
SMT_TREES="$PWD/BenchmarkResults/trees"

bash benchmark.sh --case_study PLean --with lean-smt \
  --smt_trees "$SMT_TREES" \
  --cases "Examples/PingPongTrivial.lean Examples/PingPongAuto.lean"
```

Then the full sweep, one corpus at a time. LeanHammer needs no tree of its own,
since its pinned revision already requires lean-smt:

```sh
SMT_TREES="$PWD/BenchmarkResults/trees"

bash benchmark.sh --case_study LeanHammer --with lean-smt

bash benchmark.sh --case_study PLean --with lean-smt --smt_trees "$SMT_TREES"
chmod -R u+w "$SMT_TREES/P-smt" && rm -rf "$SMT_TREES/P-smt"
git -C BenchmarkResults/sources/P-crush worktree prune

bash benchmark.sh --case_study Cashmere --with lean-smt --smt_trees "$SMT_TREES"
chmod -R u+w "$SMT_TREES/loom-smt" && rm -rf "$SMT_TREES/loom-smt"
git -C BenchmarkResults/sources/loom worktree prune

bash benchmark.sh --case_study Velvet --with lean-smt --smt_trees "$SMT_TREES"
```

Drop the `rm -rf` pairs to keep the trees; they exist because three kept trees
need about 24 GB. Lake marks some cached files read-only, so `rm -rf` alone
fails partway — hence the `chmod` first. `--case_study all` runs all four into
one result root, but holds every tree at once.

Each run writes `BenchmarkResults/reproduction-<timestamp>-lean-smt` with its
own normalized reports and plots. A run that stops partway resumes from its
per-case checkpoints, reusing the tree it already built:

```sh
bash benchmark.sh --case_study Velvet --with lean-smt \
  --smt_trees "$SMT_TREES" \
  --resume BenchmarkResults/reproduction-<timestamp>-lean-smt
```

#### Plotting Against Every Baseline

`plot-benchmarks.py` and `plot-time-coverage.py` both key rows on
`(suite, backend)`, so result directories that contribute *different* backends
for a suite combine by being listed together — no merge step. The one rule is
that no two directories may supply the same `(suite, backend)` pair, which is
why the recorded `benchmark-data/main/leanhammer` is omitted below: the
lean-smt LeanHammer run already carries all five backends for that suite.

```sh
SMT_ROOT="$PWD/BenchmarkResults/lean-smt-main"
RECORDED="$PWD/scripts/benchmark-data/main"

DIRS=(
  <leanhammer-lean-smt-dir>/leanhammer   # auto duper lean-smt crush grind
  "$RECORDED/corpora"                    # cashmere/velvet: auto duper crush grind
  <cashmere-lean-smt-dir>/cashmere       # cashmere: lean-smt
  <velvet-lean-smt-dir>/velvet           # velvet:   lean-smt
  "$RECORDED/plean"                      # plean:    auto duper crush grind
  <plean-lean-smt-dir>/plean             # plean:    lean-smt
)

python3 scripts/plot-benchmarks.py "${DIRS[@]}" \
  --out-dir "$SMT_ROOT/artifacts" \
  --exclude-suite loom \
  --only tables --only coverage --only outcomes

python3 scripts/plot-time-coverage.py "${DIRS[@]}" \
  --out-dir "$SMT_ROOT/artifacts" \
  --exclude-suite loom \
  --only main
```

Loom is excluded because its four VCs are too few for a coverage bar or a curve
to say anything; the recorded TSVs keep every corpus. `artifacts/tables.md`
carries the comparison under **Backend Comparison**, `artifacts/coverage.svg`
is the coverage figure, `artifacts/outcomes.svg` the failure breakdown, and
`artifacts/coverage-over-time.svg` the time-versus-coverage curves.

`plot-time-coverage.py` needs matplotlib, which the other renderers
deliberately do not require; both entry points warn and skip the time figure
when it is missing rather than failing the run. To replot one run in place:

```sh
bash benchmark.sh --plot_only <result-directory> --exclude_suite loom
```

### 7. Time-Versus-Coverage Figures From Recorded Data

Both time figures can also be drawn from the retained inputs under
`benchmark-data`, without rerunning a solver. The recorded directories predate
`reconstruction-comparison.tsv`, so regenerate the normalized reports into a
scratch copy first. This sequence is self-contained:

```sh
TIME_ROOT="$PWD/BenchmarkResults/paper-time-coverage"

for measurement in main crush-modes; do
  for suite in corpora leanhammer plean; do
    source_dir="scripts/benchmark-data/$measurement/$suite"
    target_dir="$TIME_ROOT/$measurement/$suite"
    mkdir -p "$target_dir"
    cp "$source_dir"/*.tsv "$target_dir/"
    python3 scripts/benchmark-report.py \
      --measurements "$target_dir/measurements.tsv" \
      --profiles "$target_dir/profile-events.tsv" \
      --out-dir "$target_dir"
  done
done

python3 scripts/plot-time-coverage.py \
  "$TIME_ROOT/main/corpora" \
  "$TIME_ROOT/main/leanhammer" \
  "$TIME_ROOT/main/plean" \
  --out-dir "$TIME_ROOT/artifacts" \
  --only main

python3 scripts/plot-time-coverage.py \
  "$TIME_ROOT/crush-modes/corpora" \
  "$TIME_ROOT/crush-modes/leanhammer" \
  "$TIME_ROOT/crush-modes/plean" \
  --out-dir "$TIME_ROOT/artifacts" \
  --only reconstruction
```

The two measurements are drawn from separate inputs for the reason given in
[Detailed Crush Measurements](#4-detailed-crush-measurements): the recorded
reconstruction study uses an earlier Velvet workload. The recorded data has no
lean-smt lane, so the reconstruction figure shows two curves until a run from
[Reconstruction Comparison](#5-reconstruction-comparison) supplies the third.
