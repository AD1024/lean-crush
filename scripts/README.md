# Benchmark Scripts

The benchmark harnesses compare the local lean-crush build with lean-auto
integrations. Generated sources, logs, metadata, per-VC measurements, and
summaries are written under `BenchmarkResults/`.

| Script | Benchmarks |
|---|---|
| `benchmark-corpora.sh` | LeanHammer, Loom, Cashmere, and Velvet |
| `benchmark-leanhammer.sh` | Standalone LeanHammer profiles |
| `benchmark-plean.sh` | PLean verification conditions |
| `with-local-crush.sh` | Runs a downstream Lean file against the local Crush build |

The latest recorded results and exact tested revisions are in
[`BENCHMARKS.md`](../BENCHMARKS.md).

## Prerequisites

Build Crush and make Z3 and cvc5 available on `PATH`:

```sh
lake build Crush
z3 --version
cvc5 --version
```

By default, place these repositories beside the lean-crush checkout:

```text
parent/
  lean-crush/
  LeanHammer/
  loom/
  velvet/
```

Override `HAMMER_REPO`, `LOOM_REPO`, or `VELVET_REPO` when using other
locations. The corpus harness creates detached worktrees for the configured
auto and Crush refs, builds their dependencies, and does not change their
checked-out branches.

## Corpus Benchmark

Run all LeanHammer, Loom, Cashmere, and Velvet cases once:

```sh
REPEATS=1 \
TIMEOUT=5 \
SOLVER=cvc5 \
CRUSH_TRUST=reconstruct \
MAX_HEARTBEATS=0 \
scripts/benchmark-corpora.sh
```

`TIMEOUT` is the solver timeout for each query. `MAX_HEARTBEATS` is the Lean
budget applied independently to each recorded VC. The generated enclosing
declaration is uncapped; the harness reports an error if a backend heartbeat
still aborts Loom's surrounding tactic traversal.

Use `MAX_HEARTBEATS=0` when complete enumeration is more important than bounded
runtime. The default one-million-heartbeat budget is useful for development
runs, but a particularly expensive VC can abort Lean's tactic traversal. The
harness detects such declaration truncation, records it in `runs.tsv`, and exits
with an error rather than publishing a partial total.

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
| `LOOM_AUTO_REF` | `origin/master` | Loom lean-auto revision |
| `LOOM_CRUSH_REF` | `origin/crush-backend` | Loom Crush revision |
| `VELVET_AUTO_REF` | `origin/master` | Velvet lean-auto revision |
| `VELVET_CRUSH_REF` | `origin/crush-backend` | Velvet Crush revision |
| `OUT_DIR` | timestamped directory | Result location |
| `USE_MATHLIB_CACHE` | `true` | Fetch Mathlib build artifacts |
| `CRUSH_PROFILE` | `false` | Include Crush phase profiling in logs |
| `KEEP_WORKTREES` | `false` | Retain temporary detached worktrees |

## LeanHammer

The standalone harness runs `auto-only`, `crush-only`, `aesop-auto`, and
`aesop-crush` over every case:

```sh
HAMMER_REPO=/path/to/LeanHammer \
REPEATS=3 \
scripts/benchmark-leanhammer.sh
```

The import-only case is recorded but excluded from its summary.

## PLean

Prepare separate vanilla and Crush-adapted PLean trees. Build both trees before
running the benchmark:

```sh
(cd /path/to/vanilla/PLean && lake build)
(cd /path/to/crush/PLean && lake build)

PLEAN_AUTO_TREE=/path/to/vanilla/PLean \
PLEAN_CRUSH_TREE=/path/to/crush/PLean \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
CRUSH_TRUST=trust \
CRUSH_INST_FUEL=0 \
scripts/benchmark-plean.sh
```

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
| `comparison.tsv` | Results and means for VCs matched across both backends |
| `file-summary.tsv` | PLean per-file coverage and timing |
| `logs/` | Complete Lean and solver output |

Do not compare raw totals when branch-specific sources emit different goals or
a run is marked truncated. Use `comparison.tsv` for matched-VC comparisons.
