# Artifact of Lean Crush

This branch contains the evaluation artifact for the Lean Crush paper. This guide
sets up an Ubuntu environment, runs the experiments, and locates the outputs
corresponding to the paper's evaluation figures and tables.

The artifact release is tagged **`tacas-ae`**. For general usage and extension APIs, see the
[Lean Crush manual](https://ad1024.github.io/lean-crush/) (Note: it is still WIP).

Archived artifact on Zenodo: [10.5281/zenodo.23456989](https://doi.org/10.5281/zenodo.23456989).

1. [Set up the environment](#1-set-up-the-environment)
2. [Run the evaluation and resume after an interruption](#2-run-the-evaluation)
3. [Generate plots and tables](#3-generate-plots-and-tables)
4. [Figures and Tables in the paper](#4-figures-and-tables-in-the-paper)

Commands marked **Host** run on the evaluation machine. Commands marked
**Container** run in the container shell opened in Step 1.

## 1. Set up the environment

### Requirements

- A Linux machine with Git and Docker installed, and permission to run Docker.
- Native amd64 or arm64 execution.
- Internet access to GitHub, package repositories, and Lean cache servers.
- Time: ~8 hours, potentially overnight or longer when dependencies must build from source.
  Budget approximately 32 GB RAM and 100 GB free disk space.

### Clone the artifact and build the image

**Host:**

```bash
git clone --branch tacas-ae https://github.com/AD1024/lean-crush.git lean-crush-artifact
cd lean-crush-artifact

docker build \
  --build-arg EVAL_UID="$(id -u)" \
  --build-arg EVAL_GID="$(id -g)" \
  --tag lean-crush-evals .
```

The UID/GID arguments
make files created in the mounted checkout belong to your host user.

The image installs Ubuntu 24.04, Lean 4.32.2 and 4.24.0, external cvc5 1.3.4,
Z3 5.1.0, Matplotlib 3.11.2, and the native compilation and PDF-rendering tools.

### Start a container and open its shell

**Host, from the checkout directory:**

```bash
docker run --detach --interactive --tty --init \
  --name lean-crush-eval \
  --mount "type=bind,source=$(pwd),target=/workspace/lean-crush" \
  lean-crush-evals bash

docker attach lean-crush-eval
```

The checkout is mounted at `/workspace/lean-crush`. Results are stored in this
checkout and persist on the host independently of the container. Keep the same
mount path when resuming: dependency environments record absolute paths.

**Container:**

```bash
cd /workspace/lean-crush
lean --version
cvc5 --version
z3 --version
python3 -c 'import matplotlib; print(matplotlib.__version__)'
rsvg-convert --version
```

These checks should succeed before starting the evaluation. The root checkout
uses Lean 4.32.2; the benchmark scripts select the other toolchain where needed.

## 2. Run the evaluation

### Smaller tests and examples

Before launching the full evaluation, build Crush and its core test suite using
the same target as the project's CI.

**Container:**

```bash
cd /workspace/lean-crush
set -o pipefail
mkdir -p BenchmarkResults

lake build Test 2>&1 | tee BenchmarkResults/sanity-check.log
ae_sanity_status=$?
printf '%s\n' "$ae_sanity_status" > BenchmarkResults/sanity-check-exit-status.txt
```

If it fails, error messages are stored in `BenchmarkResults/sanity-check.log`.

> [!NOTE]
> The running example of the paper is shown in `Test/CaseStudies/Demo.lean`.

#### Run Curated with one backend

To try the 20 Curated VCs with a single backend, run the following from the
checkout root in the **Container**. This example uses Crush with combined
Alethe replay and core-guided reconstruction:

```bash
CURATED_REPO_URL=https://github.com/AD1024/Lean-SMT-Benchmarks.git \
PROFILES=crush-portfolio \
OUT_DIR=BenchmarkResults/curated-crush/curated \
bash scripts/benchmark-curated.sh
```

The script provisions dependencies and writes measurements and reports under
`BenchmarkResults/curated-crush/curated/`. The initial dependency build may take
longer than the measurements.

Choose a `PROFILES` value below and use a separate output directory for each run:

| `PROFILES` | Backend or mode |
|---|---|
| `crush-portfolio` | Crush with Alethe replay and core-guided reconstruction |
| `crush-verify` | Crush trusting SMT results |
| `crush-alethe` | Crush with Alethe replay |
| `auto-smt` | lean-auto |
| `duper-only` | Duper |
| `grind-only` | grind |
| `smt-only` | lean-smt |

To resume an interrupted run after resolving the error and stopping the previous
process, prepend `RESUME=true` to the same command, retaining its `PROFILES` and
`OUT_DIR` values. Completed checkpoints are reused.

### Build Proof of Metatheory

Formalized metatheory is under `Crush/Metatheory`. To build this, simply run

```bash
lake build Crush.Metatheory
```

#### Main Theorems and Lemmas

The declarations below are in the namespace
`Crush.Metatheory.Defunctionalization`.

| Result in the paper (§4.2) | Corresponding Lean theorem | Detailed proof in the paper |
|---|---|---|
| Lemma 1: Preservation of denotations | [translate_denote](Crush/Metatheory/Defunctionalization/Denotation.lean#L395) | Appendix B.3 |
| Lemma 2: Validity of generated axioms | [generatedFormulas_valid](Crush/Metatheory/Defunctionalization/Theory.lean#L1031) | Appendix B.4 |
| Theorem 1: Soundness | [target_theories_unsat_implies_source_unsat](Crush/Metatheory/Soundness.lean#L28) | Appendix B.5 |

Theorem 1 uses the finite-theory result. The single-formula variant is
[target_unsat_implies_source_unsat](Crush/Metatheory/Soundness.lean#L19).

### Start a fresh run

**Container:**

```bash
set -o pipefail
mkdir -p BenchmarkResults/docker-eval

bash run-experiments.sh --out BenchmarkResults/docker-eval \
  2>&1 | tee BenchmarkResults/docker-eval/run.log
ae_status=$?
printf '%s\n' "$ae_status" > BenchmarkResults/docker-eval/exit-status.txt
```

Use `--out` once for a new output directory. The script automatically provisions the benchmark dependencies, measures all seven backends, and generates reports and plots from the new measurements.

The 4 paper benchmark suites are Curated (20 VCs), Cashmere (38), Velvet (504), and PLean
(192): **754 VCs per backend**. The 7 backends are lean-auto,
Duper, `grind`, lean-smt, Crush trusting SMT results, Crush with Alethe replay,
and Crush combining Alethe replay with core-guided reconstruction. The harness
also measures four Loom VCs, which are excluded from the paper plots and tables.

Leave the benchmark settings at their defaults. The five-second limit applies
to each SMT query (a VC may be split into multiple queries by the VCG backend). Preprocessing, proof
reconstruction, and multiple solver calls can make an attempt take longer.

> [!TIP]
> To leave the attached container session without interrupting a run, press **Ctrl-P, then Ctrl-Q**. Do not use Ctrl-C or stop the container just to detach.

**Host, to reconnect:**

```bash
docker attach lean-crush-eval
```

**Host, to inspect progress from another terminal:**

```bash
tail -f BenchmarkResults/docker-eval/run.log
```

A complete run ends with `Experiments complete: ...` and exit status `0` in
`exit-status.txt`. Individual failed proof attempts are expected benchmark
outcomes; a setup, build, or reporting error that stops the script is different
and must be resolved before treating the run as complete.

### Resume after an error or interruption

First resolve the cause, such as unavailable network access or insufficient disk
space. Preserve the existing result directory and dependency environments. Only
resume once the previous evaluation process has stopped.

If the container is still running, attach with `docker attach lean-crush-eval`.
If it has stopped, use the following **Host** command:

```bash
docker start --attach --interactive lean-crush-eval
```

Then run the following in the **Container**:

```bash
cd /workspace/lean-crush
set -o pipefail

bash run-experiments.sh --resume BenchmarkResults/docker-eval \
  2>&1 | tee -a BenchmarkResults/docker-eval/run.log
ae_status=$?
printf '%s\n' "$ae_status" > BenchmarkResults/docker-eval/resume-exit-status.txt
```

This reuses completed checkpoints and resumes unfinished setup or measurements.
An interrupted measurement without a complete checkpoint may be repeated. Do not
delete `plean-environment`, edit the checkpoints, or start over with `--out`.

For diagnosis, keep `run.log`, `build-crush.log`, the affected suite's logs, and
`plean-environment/setup.log` when present. If only plotting failed after all
measurements completed, use Step 3 instead of starting another measurement run.

## 3. Generate plots and tables

### Generate or redraw plots from your measurements

The full run already draws the plots. To regenerate reports and plots without
measuring any VCs, run in the **Container**:

```bash
bash run-experiments.sh --figures_only BenchmarkResults/docker-eval
```

Outputs are written to `BenchmarkResults/docker-eval/figures/`.

To postpone plotting during the initial run, add `--skip_figures` to the fresh-run command in Step 2, then use `--figures_only` afterward.

### Generate Table 4: replay implementation effort

This table is computed from annotated Lean source, separately from the benchmark
run. The top-level evaluation command does not generate it.

**Container:**

```bash
mkdir -p BenchmarkResults/docker-eval/figures
python3 scripts/count_replay_effort.py --format markdown \
  | tee BenchmarkResults/docker-eval/figures/implementation-effort.md
python3 scripts/count_replay_effort.py --format latex \
  > BenchmarkResults/docker-eval/figures/implementation-effort.tex
python3 scripts/count_replay_effort.py --format json \
  > BenchmarkResults/docker-eval/figures/implementation-effort.json
```

The expected totals are **55 handlers, 256 handler LoC, 797 lemma LoC, and 1,053
total LoC**. The Markdown file is directly readable; the TeX file is an includable
table, not a standalone document. JSON records the source revision and counted
regions. The counting conventions are described in
[`scripts/replay-effort.md`](scripts/replay-effort.md) under “Scope and units.”

### Generate the trusted comparison for Table 5 (Appendix D)

The default pairwise report uses Crush with proof reconstruction (Table 2).
The following optional command uses the existing reporting functions to select
trusted Crush for Table 5. It reads your saved measurements and writes a separate
TSV; it does not modify the original results or run benchmarks. Run it after the
full evaluation and report generation have completed.

**Container:**

```bash
python3 - <<'PY'
import csv
from pathlib import Path
import runpy

root = Path('BenchmarkResults/docker-eval')
report = runpy.run_path('scripts/benchmark-report.py')
with (root / 'curated/comparison.tsv').open(newline='') as stream:
    columns = next(csv.reader(stream, delimiter='\t'))
rows = []
for group in ('curated', 'corpora', 'plean'):
    source = root / group / 'measurements.tsv'
    if not source.is_file():
        raise SystemExit(f'Missing measurements: {source}')
    measurements = [row for row in report['read_tsv'](source)
                    if row['suite'] != 'loom' and row['lane'] != 'crush-portfolio']
    attempts = report['grouped_attempts'](measurements)
    report['validate_uniform_headline'](attempts)
    rows.extend(report['comparison_rows'](attempts))
output = root / 'figures/comparison-trusted.tsv'
report['write_tsv'](output, columns, rows)
print(output)
PY
```

The `crush_lane` column should be `crush-verify`. Tables 2 and 5 are provided as
numerical TSV/Markdown reports.

## 4. Figures and Tables in the paper

All paths below are relative to **`BenchmarkResults/docker-eval/`**, visible both
inside the container and in the host checkout. Open the PDFs and Markdown files
on the host; no graphical viewer is required inside the container.

### Matching tables and figures

In figures and tables shown in the following files, `crush-portfolio` enables both core-guided and Alethe replay proof reconstruction; `crush-alethe` enables only Alethe replay; `crush-verify` trusts the SMT verdict.

| Paper location | Output to inspect | How to read it |
|---|---|---|
| **Figure 11, §6.1:** verification coverage and runtime | `figures/coverage-over-time-curated.pdf`, `figures/coverage-over-time-cashmere.pdf`, `figures/coverage-over-time-velvet.pdf`, `figures/coverage-over-time-plean.pdf` | The four panels are separate PDFs, in paper reading order. Curve coordinates are in `figures/coverage-over-time.tsv`. |
| **Table 2, §6.2:** pairwise comparison with proof reconstruction | `figures/tables.md`, heading **Pairwise Matched VCs**; `comparison.tsv` in each of `curated/`, `corpora/`, and `plean/` | Use `crush-portfolio`. Read Crush-only, baseline-only, both-solved counts, and mean/SD times on the both-solved VCs. Exclude the raw TSV rows for `loom`. |
| **Figure 12, §6.3:** proof reconstruction coverage | `figures/reconstruction-over-time-curated.pdf`, `figures/reconstruction-over-time-cashmere.pdf`, `figures/reconstruction-over-time-velvet.pdf`, `figures/reconstruction-over-time-plean.pdf` | Separate PDFs for the four panels. Curve coordinates are in `figures/reconstruction-over-time.tsv`. |
| **Table 3, §6.3:** proof reconstruction failures | `figures/reconstruction-failures-table.pdf`; `figures/tables.md`, heading **Reconstruction Failures**; each suite directory's `reconstruction-failures.tsv` | The artifact breaks failures down by suite. The paper aggregates across its four suites, separately for Alethe replay and combined reconstruction. Use `reconstruction-summary.tsv` for the SMT-discharged cohort denominators. |
| **Table 4, §6.3:** replay implementation effort | `figures/implementation-effort.md`, `.tex`, and `.json` | Generated separately by the Table 4 commands in Step 3; no benchmark measurements are needed. |
| **Table 5, Appendix D:** trusted SMT pairwise comparison | `figures/comparison-trusted.tsv` | Generated by the optional Table 5 command in Step 3; uses `crush-verify` rather than `crush-portfolio`. |

### Raw results and completeness checks

| Location | Contents |
|---|---|
| `run.log`, `exit-status.txt`, `resume-exit-status.txt` when applicable | Console output and exit status recorded by the commands above. Check the most recent invocation's status. |
| `curated/`, `corpora/`, `plean/` | Measurements, reports, profiling data, logs, and checkpoints. Cashmere and Velvet share `corpora/`, distinguished by the `suite` column. |
| Each group's `measurements.tsv` | Per-VC backend, identity, final status, elapsed time, and diagnostics. |
| Each group's `coverage-summary.tsv` | Expected, attempted, solved, failed, and missing VC counts for each suite/backend. |
| Each group's `reconstruction-comparison.tsv` | Final kernel-checked proof counts for the compared reconstruction methods. |
| Each group's `profile-events.tsv` | Intermediate translation, solver, and reconstruction events for detailed inspection. |
| `plean-environment/` | Automatically provisioned PLean environment and setup records; preserve it for resuming. |

> [!NOTE]
> The paper reports measurements from an Apple M1 Pro with 32 GB memory. Ubuntu
> timings will vary with hardware and load, and timeout-sensitive proof outcomes may vary between runs.

### Optional: Reference results

To render the archived reference measurements rather than your new results,
run the following in the **Container**:

```bash
bash scripts/render-paper-artifacts.sh BenchmarkResults/reference-figures
```

This reads `scripts/benchmark-data/eval-data.zip` and writes a separate directory.
It is useful for inspecting the supplied results, but is **not a fresh
reproduction**. Keep it separate from `BenchmarkResults/docker-eval/`; do not
use archived rows to fill missing measurements in a new run.

## Further information

- [Benchmark scripts](scripts/README.md): individual runners and advanced options.
- [Dockerfile](Dockerfile): environment setup and compiler-header fix.
- [Pinned PLean environment](scripts/benchmark-data/plean-shared-lock.json):
  dependency revisions and toolchain settings.
- [Mechanized metatheory](Crush/Metatheory/README.md) and [Lean examples](Test/).
