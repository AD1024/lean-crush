# Benchmark Scripts

Everything the paper's figures and tables need comes from one script:

```sh
bash run-experiments.sh
```

It measures every lane on every case study into one dataset and draws every
figure from it. Nothing is recorded in the repository that it did not produce,
and there is no merge step afterwards -- which is the point. The lanes used to
be split across three overlapping runs, and because a `(suite, lane)` could
appear in more than one, the copies drifted: Velvet's Alethe rows were post-fix
in one and pre-fix in another, so a figure said 239 checked VCs while the prose
said 196. Measured once, a lane cannot disagree with itself.

| Script | Role |
|---|---|
| `../run-experiments.sh` | **Everything: measures all lanes, then draws all figures** |
| `benchmark-curated.sh` | One suite: the curated obligations, one backend per branch |
| `benchmark-corpora.sh` | One suite: Loom, Cashmere, Velvet |
| `benchmark-plean.sh` | One suite: PLean |
| `render-paper-artifacts.sh` | Draws every figure from a dataset |
| `merge-runs.py` | Joins suites measured in separate runs |

The three per-suite harnesses are what `run-experiments.sh` calls. Run them
directly when iterating on one corpus; run the top-level script when you want
the dataset the paper uses.

## Prerequisites

```sh
git --version
lake --version
z3 --version
cvc5 --version
python3 -c "import matplotlib"   # must succeed, or the curve figures are skipped
```

If that check fails, matplotlib is missing from whichever `python3` comes first
on `PATH`, and that is the interpreter the scripts use. A system or Homebrew
python will refuse `pip install` under PEP 668, so either use a virtualenv that
has it, or install for the user:

```sh
python3 -m pip install --user matplotlib
```

Do not reorder `PATH` to fix a solver, because that can change which python3 you
get. Pin the solvers by variable instead and leave `PATH` alone:

```sh
Z3_BIN=/opt/homebrew/bin/z3 CVC5_BIN=/path/to/cvc5 bash run-experiments.sh
```

`find_solver` prefers those variables over `PATH`, so this picks the solver you
want without disturbing the interpreter. Without matplotlib the runs still
complete and the bar charts and tables are unaffected, but
`coverage-over-time-<suite>.pdf` is not drawn; the renderer names the
interpreter it tried and lists what it skipped.

The harnesses clone pinned revisions into `BenchmarkResults/sources` and build
every downstream package, so a fresh run needs network access but no manually
prepared checkouts. Set `BENCHMARK_SOURCE_CACHE` to clone elsewhere, or point
`CURATED_REPO`, `LOOM_REPO`, `VELVET_REPO`, `PLEAN_AUTO_TREE`,
`PLEAN_DUPER_TREE`, and `PLEAN_CRUSH_TREE` at existing ones.

If a virtualenv is active, check `which -a z3`: a shadowed older z3 changes
results. Pass `Z3_BIN` and `CVC5_BIN` to pin the binaries.

The lean-smt lane is the exception to all of this. It calls cvc5 through the
in-process bindings its Lake package links, so it uses neither the `cvc5` on
`PATH` nor `CVC5_BIN`, and it refuses to run under `SOLVER=z3`.

## 1. Run the experiments

```sh
bash run-experiments.sh
```

Writes `BenchmarkResults/experiments-<stamp>/` holding `curated/`, `corpora/`,
`plean/` and `figures/`. Every lane the paper reports is measured: Auto, Duper,
`grind`, lean-smt, and Crush's trusted, strict-Alethe and portfolio lanes.

| Option | Meaning |
|---|---|
| `--out <dir>` | Write somewhere other than the timestamped default |
| `--resume <dir>` | Continue into an existing dataset, skipping finished cases |
| `--suites "<names>"` | Subset of `curated corpora plean` |
| `--skip_figures` | Measure only |
| `--figures_only <dir>` | Redraw a finished dataset, measuring nothing |
| `--update_archive` | Also refresh `scripts/benchmark-data/eval-data.zip` |

| Variable | Default | Effect |
|---|---|---|
| `REPEATS` | `1` | Repeats per VC; one for every case study |
| `SOLVER` | `cvc5` | lean-smt cannot run under z3, so the run refuses anything else |
| `TIMEOUT` | `5` | Per-query solver seconds |
| `CRUSH_MODES` | `verify alethe portfolio` | Add `core` to fill the Core column |
| `CURATED_TREES` | `BenchmarkResults/curated-trees` | One Lake build per Curated branch |
| `SMT_TREE_ROOT` | `BenchmarkResults/trees` | lean-smt worktrees, one per corpus |
| `Z3_BIN`, `CVC5_BIN` | from `PATH` | Pin the solver binaries |

Both tree variables are worth pointing at a stable path. Each directory holds a
Lake build, and keeping them between runs is the difference between minutes and
hours; deleting one forces that build again.

A first run provisions every corpus and builds every tree, so budget hours for
it. `--resume` makes an interrupted run cheap to continue, and `--suites`
narrows it to one corpus while iterating.

## 2. Draw the figures

Step 1 already draws them. To redraw without measuring:

```sh
bash run-experiments.sh --figures_only BenchmarkResults/experiments-<stamp>
```

The renderer draws a figure when the lanes it needs are present and says what
it skipped otherwise, so a dataset measured with `--suites` still renders what
it covers.

Coverage figures: `coverage.pdf`, `coverage-table.pdf`, `outcomes.pdf`,
`coverage-over-time-<suite>.pdf`. Reconstruction figures: `reconstruction.pdf`,
`reconstruction-table.pdf`, `reconstruction-failures{,-table}.pdf`,
`reconstruction-over-time-<suite>.pdf`, `alethe-replay-scaling-<suite>.pdf`,
`phase-breakdown.pdf`. Plus `tables.md`, from which the recorded tables in
[`BENCHMARKS.md`](../BENCHMARKS.md) are taken.

To draw from a dataset that is not a run directory -- the committed archive,
say -- point the renderer at it:

```sh
mkdir -p /tmp/eval && unzip -q scripts/benchmark-data/eval-data.zip -d /tmp/eval
MEASUREMENTS_ROOT=/tmp/eval bash scripts/render-paper-artifacts.sh out/
```

## 3. One suite at a time

`run-experiments.sh` calls these; use them directly when iterating.

```sh
PROFILES="crush-verify crush-alethe crush-portfolio smt-only grind-only duper-only auto-smt" \
OUT_DIR=<dir>/curated bash scripts/benchmark-curated.sh

RUN_CURATED=false RUN_SMT=true CRUSH_MODES="verify alethe portfolio" \
OUT_DIR=<dir>/corpora bash scripts/benchmark-corpora.sh

RUN_SMT=true CRUSH_MODES="verify alethe portfolio" \
OUT_DIR=<dir>/plean bash scripts/benchmark-plean.sh
```

Each writes one directory holding `measurements.tsv`, `profile-events.tsv` and
the reports regenerated from them. A dataset is just those directories side by
side, which is why no merge step exists.

The curated suite keeps one backend per branch of
[Lean-SMT-Benchmarks](https://github.com/AD1024/Lean-SMT-Benchmarks), so that no
backend's dependencies reach another's environment:

| Branch | Lane |
|---|---|
| `main` | `grind-only` |
| `auto` | `auto-smt` (lean-auto translating to SMT-LIB and querying cvc5) |
| `duper` | `duper-only` |
| `lean-smt` | `smt-only` |
| `crush` | `crush-verify`, `crush-core`, `crush-alethe`, `crush-portfolio` |

Each branch needs its own Lake build, kept under `CURATED_TREES`. The harness
clones over SSH; set `CURATED_REPO_URL` to the `https://` form to clone
anonymously, or `CURATED_REPO` to a checkout you already have. The `lean-smt`
branch fixes its solver configuration in its own harness, because lean-smt takes
it as tactic syntax rather than as an option, so `SMT_TIMEOUT` and `SMT_MONO`
must be left at 5 and `true` or the run refuses to start.

For Velvet, Cashmere and PLean the lean-smt lane applies a recorded patch from
[`patches`](patches) that adds the dependency to the pinned revision, then
verifies that resolving it moved nothing else.

## What reproduces

Coverage reproduces across machines. **Timings do not.** The external solver
call is the part that moves most, and VCs sitting near the 5s cvc5 cap can flip
between runs on the same host. Compare per-VC times only within one run.

To narrow a run before committing to a full one: `--suites` measures one case
study, and `CRUSH_MODES` drops Crush lanes. Either gives a subset, not the
published measurement.
