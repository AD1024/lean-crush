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
| `benchmark-plean-shared.py` | PLean: shared scaffold for all seven lanes |
| `setup-plean-shared.py` | Automatically provision isolated, pinned PLean dependencies and compiler builds |
| `prepare-plean-shared.py` | Generate matching modern and Auto-compatible PLean sources |
| `benchmark-plean.sh` | Legacy PLean driver; its input-generation helper is reused by the shared runner |
| `render-paper-artifacts.sh` | Draws every figure from a dataset |
| `merge-runs.py` | Joins suites measured in separate runs |

The three per-suite harnesses are what `run-experiments.sh` calls. Run them
directly when iterating on one corpus; run the top-level script when you want
the dataset the paper uses.

## Prerequisites

```sh
git --version
elan --version
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
Z3_BIN=/opt/homebrew/bin/z3 CVC5_BIN=/path/to/cvc5 \
  bash run-experiments.sh
```

For Curated and the corpora, `find_solver` prefers those variables over `PATH`.
PLean setup downloads cvc5 1.3.4 or copies an explicitly supplied `CVC5_BIN`,
verifies its version (and its recorded binary checksum on macOS arm64), and
records the isolated solver path. Without matplotlib the runs still
complete and the bar charts and tables are unaffected, but
`coverage-over-time-<suite>.pdf` is not drawn; the renderer names the
interpreter it tried and lists what it skipped.

The Curated and corpora harnesses clone pinned revisions into
`BenchmarkResults/sources` and build downstream packages. Set
`BENCHMARK_SOURCE_CACHE` to clone elsewhere, or point `CURATED_REPO`,
`LOOM_REPO`, and `VELVET_REPO` at existing ones. PLean instead consumes a
shared environment provisioned automatically when PLean is reached, described
below; its measurement runner never resolves dependencies or modifies build trees.

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
| `--plean-config <file>` | Optional prepared environment override; default setup is automatic |
| `--skip_figures` | Measure and generate report TSVs, without plotting |
| `--figures_only <dir>` | Regenerate reports and redraw a dataset, measuring nothing |
| `--update_archive` | Also refresh `scripts/benchmark-data/eval-data.zip` |

| Variable | Default | Effect |
|---|---|---|
| `REPEATS` | `1` | Repeats per VC; one for every case study |
| `SOLVER` | `cvc5` | lean-smt cannot run under z3, so the run refuses anything else |
| `TIMEOUT` | `5` | Per-query solver seconds |
| `CRUSH_MODES` | `verify alethe portfolio` | Adjustable for Curated/corpora; fixed for shared PLean |
| `CURATED_TREES` | `BenchmarkResults/curated-trees` | One Lake build per Curated branch |
| `SMT_TREE_ROOT` | `BenchmarkResults/trees` | lean-smt worktrees, one per corpus |
| `Z3_BIN`, `CVC5_BIN` | from `PATH` | Pin the solver binaries |
| `PLEAN_SHARED_CONFIG` | unset | Environment-file alternative to `--plean-config` |

PLean fixes one repeat, a 5s solver timeout, 1,000,000 heartbeats and recursion
depth, 20 `grind` splits, and the three listed Crush modes. The top-level script
rejects incompatible overrides when PLean is selected. PLean's solver paths
come from its environment file. An explicit `--plean-config` retains those
recorded paths; automatic setup can copy a supplied `CVC5_BIN` as described above.

Both tree variables are worth pointing at a stable path. Each directory holds a
Lake build, and keeping them between runs is the difference between minutes and
hours; deleting one forces that build again.

A first run provisions Curated and the corpora and uses the prepared PLean
environment, so budget hours for it. `--resume` skips completed cases, and
`--suites` narrows the run to one corpus. A PLean-only run does not rebuild
Crush. Cleanup preserves any build tree referenced by the PLean environment.

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

bash run-experiments.sh --suites plean --skip_figures --out <dir>
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

For Velvet and Cashmere the lean-smt lane applies a recorded patch from
[`patches`](patches) that adds the dependency to the pinned revision, then
verifies that resolving it moved nothing else.

### PLean shared scaffold

`run-experiments.sh` invokes `benchmark-plean-shared.py` for PLean, with no
fallback to the legacy per-backend harness. `prepare-plean-shared.py` generates
both build trees from P revision `9c098b4c5ad32faf2a022929b6726d2a182a9e1d`.
The proof scaffold and VC generator are byte-identical across backends. Auto
retains Lean 4.24.0 for compatibility; the other lanes use Lean 4.32.2. Only the
backend dispatcher and counterexample-formatting adapters differ between the
trees. The runner checks source hashes and saves `scaffold-audit.json` before
measurement. All lanes consume the same generated example files.

WP generation, normalization, conjunction and conditional splits, the case
analysis in `default_inv`, and frame walking remain. Auxiliary `grind`, `omega`,
`tauto`, `solve_by_elim`, `assumption`, and `trivial` calls are replaced with the
selected backend. Backend-internal automation is unchanged. Deterministic
proof steps, including simplification and explicit lemma applications, remain.

`PLEAN_BENCH` records whether the final proof uses a backend proof or closes
through scaffolding alone. Backtracked attempts do not establish attribution.
New timing measures the whole obligation tactic, including failed attempts;
it is not directly comparable with the old phase-sum timings. Patched sources
are saved alongside each run. Use a fresh output directory; the harness rejects
resuming the older measurements under this policy. Existing published data is
not overwritten by changing the harness.

Automatic setup writes `<dataset>/plean-environment/run-config.json`. Its
inputs are pinned in `benchmark-data/plean-shared-lock.json`; Mathlib's
transitive dependencies use the exact commits in its pinned manifest. Setup
installs the two Lean toolchains through elan, checks out independent Git
repositories, obtains the Mathlib caches (or builds from source), builds the
native cvc5 binding, Auto with its native Lake plugins, and PLean imports,
and checks imports and the embedded solver
version through its native binding. It does
not build or execute the example obligations. Git, elan, Python 3.10+, a C/C++
toolchain, and network access are required; plotting additionally uses the
dependencies listed above. No existing developer checkout or temporary build
cache is required.
Mathlib and Lake caches are owned by the setup directory. On macOS, SDK discovery
supplies the C++ and compiler header paths needed by Lean's bundled clang.
Archive tools use the portable `C` locale. When an older Mathlib manifest pins
a ProofWidgets release tag, setup fetches the tag and verifies that it names
the same pinned commit before requesting the release cache.

The generated source bundle must match the hashes recorded for the measured
shared scaffold. Setup writes commands to `setup.log`, records dependency
revisions and compiler/solver hashes in `provisioning-manifest.json`, and refuses
to overwrite foreign environments or modified dependency sources. The
environment JSON records `modern` and `auto` build paths, compiler paths,
library paths and the native binding. These absolute paths belong to the
chosen output directory; reproduce in a new location through the same setup
command, rather than copying an old path manifest.

The runner reads the 192 VC identities directly from the shipped
`benchmark-data/eval-data.zip`; no extracted `BenchmarkResults/paper` directory
is required. Reports are regenerated from raw measurements before plotting,
including when using `--figures_only`. `--skip_figures` still writes report TSVs.

```sh
bash run-experiments.sh --suites plean --skip_figures \
  --out BenchmarkResults/shared-plean-new-run

bash run-experiments.sh --suites plean --skip_figures \
  --resume BenchmarkResults/shared-plean-new-run
```

Each completed file has a JSON checkpoint. Resume reuses the recorded
environment and skips those files; it rejects legacy PLean output directories
and a different environment file. The top-level script writes PLean results
under `<dir>/plean/`, as expected by the existing figure renderer.
To verify provisioning separately, without starting any measurements:

```sh
python3 scripts/setup-plean-shared.py --out BenchmarkResults/clean-plean-environment
```

Then optionally supply that directory's `run-config.json` with `--plean-config`.
Do not perform an expensive clean build concurrently with timing measurements.
Source-hash and import-only checks validate setup; they do not constitute an
independent repetition of the experiment.

Reports count final VC proofs consistently across backends. An intermediate
failed attempt does not invalidate a later final proof. Proof provenance is
reported separately, distinguishing backend proofs from scaffold proofs.
Use `run-experiments.sh --figures_only <dataset>` to regenerate reports and
figures without setup or measurement. One-off migration, audit, and pilot
tools are not part of the reproduction workflow.

## What reproduces

Timings depend on the machine, and VCs near the 5s cvc5 cap can change success
status even between runs on the same host. Compare per-VC times within one run.

To narrow a run before committing to a full one, `--suites` selects case
studies. For Curated and the corpora, `CRUSH_MODES` can also drop Crush lanes;
the shared PLean runner measures all seven lanes.
