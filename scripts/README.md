# Benchmark Scripts

The benchmark harnesses compare lean-auto, Duper, and the local lean-crush
build. Generated sources, logs, metadata, per-VC measurements, and summaries
are written under `BenchmarkResults/`.

| Script | Benchmarks |
|---|---|
| `benchmark-corpora.sh` | LeanHammer, Loom, Cashmere, and Velvet |
| `benchmark-leanhammer.sh` | Standalone LeanHammer profiles |
| `benchmark-plean.sh` | PLean verification conditions |
| `benchmark-common.sh` | Shared pinned-source provisioning |
| `with-local-crush.sh` | Runs a downstream Lean file against the local Crush build |

The latest recorded results and exact tested revisions are in
[`BENCHMARKS.md`](../BENCHMARKS.md).

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
CRUSH_TRUST=reconstruct \
MAX_HEARTBEATS=1000000 \
OUT_DIR="$PWD/BenchmarkResults/corpora-reproduction" \
scripts/benchmark-corpora.sh
```

`TIMEOUT` is the solver timeout for each query. `MAX_HEARTBEATS` is the Lean
budget applied independently to each recorded VC. The generated enclosing
declaration is uncapped; the harness reports an error if a backend heartbeat
still aborts Loom's surrounding tactic traversal.

This is the configuration used for the recorded table. It produces known
truncation warnings for some Velvet files and exits nonzero after writing all
reports. `matched-summary.tsv` still contains the valid 355-VC intersection
used by the headline comparison. Use `MAX_HEARTBEATS=0` for a new run where
complete enumeration is more important than matching the recorded bounds.
The harness records any truncation in `runs.tsv` and rejects raw partial totals.

For performance measurements, use multiple repeats:

```sh
REPEATS=3 MAX_HEARTBEATS=0 scripts/benchmark-corpora.sh
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
| `USE_MATHLIB_CACHE` | `true` | Fetch Mathlib build artifacts |
| `CRUSH_PROFILE` | `false` | Include Crush phase profiling in logs |
| `KEEP_WORKTREES` | `false` | Retain temporary detached worktrees |

## LeanHammer

The standalone harness runs `duper-only`, `auto-duper`, `crush-only`,
`aesop-auto-duper`, and `aesop-crush` over every case:

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

Run all three published PLean lanes:

```sh
RUN_DUPER=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
CRUSH_TRUST=trust \
CRUSH_INST_FUEL=0 \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=60 \
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
`DUPER_MAX_HEARTBEATS=20000`, plus a
`DUPER_FILE_CPU_SECONDS=60` limit on each generated Lean file. One million
heartbeats made the first file run for over 40 minutes, while `200000` still
exceeded 18 minutes. This is a bounded stress-test lane, not an equal-resource
timing comparison. Set `DUPER_FILE_CPU_SECONDS=0` to remove the file limit.
Set `PREPARE_TREES=false` only when all selected override trees and their
dependencies are already built.

The Duper lane is opt-in because five of the nine PLean files reach that CPU
limit. Each file runs in a separate process, so all nine are attempted:

```sh
RUN_AUTO=false \
RUN_CRUSH=false \
RUN_DUPER=true \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=60 \
REPEATS=1 \
OUT_DIR="$PWD/BenchmarkResults/plean-duper-stress" \
scripts/benchmark-plean.sh
```

The focused command writes only Duper results. Use the all-lanes command above
to generate the PLean auto/Duper/Crush rows in `comparison.tsv`.

The PLean harness disables registered manual proofs in temporary generated
sources so both backends attempt every VC. It excludes incomplete
`Paxos.lean`; override `PLEAN_CASES` to select a space-separated file list.

## Outputs

The corpus and PLean harnesses write:

| File | Contents |
|---|---|
| `metadata.tsv` | Revisions, toolchains, solver configuration, and dirty state |
| `results.tsv` | Per-VC status, failure category, and tactic-local time |
| `runs.tsv` | Per-file wall time, exit status, and VC count; corpus runs also record truncation |
| `summary.tsv` | Coverage and aggregate attempted-VC timing |
| `matched-summary.tsv` | Corpus-only coverage and timing on the three-backend VC intersection |
| `comparison.tsv` | Pairwise results and means for VCs matched across each available backend pair |
| `file-summary.tsv` | PLean-only per-file coverage and timing |
| `logs/` | Complete Lean and solver output |

Do not compare raw totals when branch-specific sources emit different goals or
a run is marked truncated. Use `comparison.tsv` for matched-VC comparisons.
