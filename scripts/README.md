# Benchmark Scripts

How to re-run the experiments and draw the figures. Everything is written under
`BenchmarkResults/`, which is gitignored apart from the recorded archive.

| Script | What it measures |
|---|---|
| `../benchmark-coverage.sh` | **Coverage comparison: every backend, then the figures** |
| `../benchmark.sh` | One backend and case study |
| `../benchmark-crush-modes.sh` | Crush's trusted, Core, Alethe, and portfolio lanes |
| `../benchmark-reconstruction.sh` | lean-smt against Crush's Alethe and portfolio lanes |
| `render-paper-artifacts.sh` | Draws every published figure from a dataset |
| `merge-runs.py` | Combines run directories and regenerates their reports |
| `fold-crush-series.py` | Replaces a dataset's Crush lanes from a mode study |

The recorded results are in [`BENCHMARKS.md`](../BENCHMARKS.md) and their inputs
in [`benchmark-data`](benchmark-data). The 2026-08-20 snapshot is kept in
[`BenchmarkResults/recorded/2026-08-20`](../BenchmarkResults/recorded/2026-08-20).

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
Z3_BIN=/opt/homebrew/bin/z3 CVC5_BIN=/path/to/cvc5 bash benchmark-coverage.sh ...
```

`find_solver` prefers those variables over `PATH`, so this picks the solver you
want without disturbing the interpreter. Without matplotlib the runs still
complete and the bar charts and tables are unaffected, but
`coverage-over-time-<suite>.pdf` is not drawn; the renderer names the
interpreter it tried and lists what it skipped.

The harnesses clone pinned revisions into `BenchmarkResults/sources` and build
every downstream package, so a fresh run needs network access but no manually
prepared checkouts. Set `BENCHMARK_SOURCE_CACHE` to clone elsewhere, or point
`HAMMER_REPO`, `LOOM_REPO`, `VELVET_REPO`, `PLEAN_AUTO_TREE`,
`PLEAN_DUPER_TREE`, and `PLEAN_CRUSH_TREE` at existing ones.

If a virtualenv is active, check `which -a z3`: a shadowed older z3 changes
results. Pass `Z3_BIN` and `CVC5_BIN` to pin the binaries.

The lean-smt lane is the exception to all of this. It calls cvc5 through the
in-process bindings its Lake package links, so it uses neither the `cvc5` on
`PATH` nor `CVC5_BIN`, and it refuses to run under `SOLVER=z3`.

## 1. Run the coverage comparison

```sh
bash benchmark-coverage.sh --case_study all
```

This is the whole path: it measures every backend into one directory and then
draws the figures. `benchmark.sh` measures one backend per invocation into its
own directory, which cannot produce a cross-backend figure.

Output lands in `BenchmarkResults/coverage-<timestamp>/`, with one subdirectory
per case study and the figures under `figures/`. Crush is measured in both
lanes, so the run yields the `Crush (SMT trusted)` and `Crush (kernel-checked)`
series together.

Check the path on one file first

```sh
BACKENDS=grind bash benchmark-coverage.sh --case_study Cashmere \
  --cases "CaseStudies/Cashmere/CashmereIncorrectnessLogic.lean"
```

| Argument | Meaning |
|---|---|
| `--case_study <all\|LeanHammer\|Velvet\|Cashmere\|PLean>` | Required |
| `--cases "<file> ..."` | Restrict to named files; needs a single `--case_study` |
| `--resume <dir>` | Continue into an existing run directory |
| `--figures_only <dir>` | Redraw a finished run, measuring nothing |
| `--skip_figures` | Measure only |

| Variable | Default |
|---|---|
| `BACKENDS` | `crush auto duper grind lean-smt` |
| `CRUSH_LANES` | `verify portfolio` |
| `SMT_TREES` | unset; names a directory to keep lean-smt worktrees between runs |
| `Z3_BIN`, `CVC5_BIN` | resolved from `PATH` |

Drop the slowest lane with `BACKENDS="crush auto duper grind"`. Each lean-smt
tree carries its corpus's Mathlib build plus lean-smt's, so `SMT_TREES` is worth
setting if you will run it more than once.

## 2. Draw the figures

Step 1 already draws them. To redraw without measuring:

```sh
bash benchmark-coverage.sh --figures_only BenchmarkResults/coverage-<timestamp>
```

To draw from the recorded data instead of your own run:

```sh
bash scripts/render-paper-artifacts.sh            # into BenchmarkResults/figures
bash scripts/render-paper-artifacts.sh out/       # or a directory you name
```

Every recorded measurement ships in one archive,
[`benchmark-data/eval-data.zip`](benchmark-data/eval-data.zip), holding `main/`,
`crush-modes/` and `reconstruction/`. The renderer unpacks it to a temporary
directory, so refreshing the data is one binary change rather than several
hundred file additions and deletions.

| Variable | Default | Effect |
|---|---|---|
| `PAPER_DATA_ARCHIVE` | `scripts/benchmark-data/eval-data.zip` | The archive to unpack |
| `PAPER_DATA_ROOT` | unset | Read loose directories instead of the archive |
| `MAIN_ROOT` | `<data>/main` | Coverage comparison inputs |
| `MODES_ROOT` | `<data>/crush-modes` | Crush-mode inputs |
| `RECONSTRUCTION_ROOT` | `<data>/reconstruction` | Cross-tool inputs |

Each root is scanned for subdirectories holding a `measurements.tsv`, so both a
full `--case_study all` run and a single-case-study run render. Missing
`MODES_ROOT` or archive data skips those figures rather than failing.

Coverage figures: `coverage.pdf`, `coverage-table.pdf`, `outcomes.pdf`,
`coverage-over-time-<suite>.pdf`, and `tables.md`. The reconstruction figures
come from the studies in step 3 and are skipped by `benchmark-coverage.sh`,
which draws only what its own run measured.

## 3. The other studies

Crush's reconstruction lanes against each other:

```sh
bash benchmark-crush-modes.sh --case_study all
bash benchmark-crush-modes.sh --case_study all --resume <dir>
bash benchmark-crush-modes.sh --plot_only <dir>
```

`CRUSH_MODES` selects lanes, default `verify core alethe portfolio`. The
reconstruction table is computed against the trusted lane, so `verify` must be
present or the report comes out empty.

Crush against lean-smt on checked reconstruction. This is the slowest study,
because each corpus needs a lean-smt tree carrying its own Mathlib build plus
lean-smt's, so `--smt_trees` is worth passing:

```sh
bash benchmark-reconstruction.sh --case_study all --smt_trees BenchmarkResults/trees
bash benchmark-reconstruction.sh --case_study <one> --cases "<file> ..."
bash benchmark-reconstruction.sh --plot_only <dir> [--exclude_suite <corpus>]
```

It produces `reconstruction-over-time-<suite>.pdf` and `reconstruction-table.pdf`,
which no other study can produce: they need `smt-only` measured beside Crush's
Alethe and portfolio lanes in one run, and the Crush-mode data has no lean-smt
lane. Draw them from a run with:

```sh
RECONSTRUCTION_ROOT=BenchmarkResults/reconstruction-<timestamp> \
  bash scripts/render-paper-artifacts.sh
```

To make a run the committed default, rebuild the archive with that study's
directory replaced:

```sh
mkdir -p /tmp/eval && unzip -q scripts/benchmark-data/eval-data.zip -d /tmp/eval
rm -rf /tmp/eval/reconstruction
cp -R BenchmarkResults/reconstruction-<timestamp> /tmp/eval/reconstruction
rm -f /tmp/eval/reconstruction/*/*.log
(cd /tmp/eval && rm -f old.zip && \
  zip -rq "$OLDPWD/scripts/benchmark-data/eval-data.zip" main crush-modes reconstruction)
```

Substitute `main` or `crush-modes` for the other two studies. Each holds suite
directories at its top level; the renderer passes each to the plotter.

One backend on its own:

```sh
bash benchmark.sh --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
  --with <crush|auto|duper|grind|lean-smt> [--smt_trees <dir>]
bash benchmark.sh --case_study <one> --with <backend> --cases "<file> ..."
bash benchmark.sh --case_study all --with crush --resume <dir>
bash benchmark.sh --plot_only <dir> [--exclude_suite <corpus>]
```

`--exclude_suite` omits a corpus from tables and figures; repeat to omit
several. The published figures exclude `loom`, whose four VCs are too few for a
coverage bar to say anything. The recorded TSVs always keep every corpus.

For Velvet, Cashmere, and PLean the lean-smt lane applies a recorded patch from
[`patches`](patches) that adds the dependency to the pinned revision, then
verifies that resolving it moved nothing else.

## 4. Combining runs

Suites measured separately live in separate directories. To join them — for
example `cashmere/` and `velvet/` into the `corpora/` layout the datasets use:

```sh
python3 scripts/merge-runs.py <run>/cashmere <run>/velvet --out <dest>/corpora
```

Only raw inputs are concatenated; every derived TSV is regenerated from them, so
no summary can disagree with its rows. Suites must be disjoint — `--replace`
lets a later source supersede an earlier one's suites.

To swap a dataset's Crush lanes for a newer run's:

```sh
python3 scripts/fold-crush-series.py --target <dataset>/<suite> \
  --donor <run>/<suite> --report scripts/benchmark-report.py
```

## What reproduces

Coverage reproduces across machines. **Timings do not.** The external solver
call is the part that moves most, and VCs sitting near the 5s cvc5 cap can flip
between runs on the same host. Compare per-VC times only within one run.

To narrow a run before committing to a full one: `--cases` restricts to named
files, `BACKENDS` drops lanes, and a single `--case_study` measures one corpus.
Any of those gives a subset, not the published measurement.
