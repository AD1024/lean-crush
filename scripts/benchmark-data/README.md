# Paper reference data

`eval-data.zip` contains the saved measurements used in the paper, together with
reports regenerated from those measurements. It is reference data, not the
output of a new reproduction run.

| Directory in the archive | Contents |
|---|---|
| `curated/` | Curated: 20 VCs |
| `corpora/` | Cashmere: 38 VCs; Velvet: 504 VCs; four additional Loom VCs excluded from the paper |
| `plean/` | PLean: 192 VCs, measured with the shared scaffolding |

The four paper benchmarks contain 754 VC identities, each measured with seven
backends or Crush modes. `measurements.tsv` records final VC outcomes and
timings; `profile-events.tsv` records intermediate events. The other TSVs are
derived reports or historical measurement metadata. Intermediate failures do
not override a successful final VC outcome.

## Reference counts

| Backend or mode | Curated | Cashmere | Velvet | PLean | Total |
|---|---:|---:|---:|---:|---:|
| Crush, trusted | 19 | 38 | 478 | 174 | 709 |
| Crush, Alethe + core-guided reconstruction | 19 | 38 | 472 | 164 | 693 |
| Crush, Alethe replay | 14 | 9 | 215 | 3 | 241 |
| lean-auto | 17 | 18 | 415 | 172 | 622 |
| Duper | 12 | 21 | 291 | 89 | 413 |
| lean-smt | 12 | 17 | 302 | 100 | 431 |
| grind | 16 | 19 | 444 | 162 | 641 |

Head-to-head timing summaries use VCs discharged by both tools and report the
mean and sample standard deviation. The reconstruction-failure table uses the
503 VCs with recorded SMT success: Alethe replay has 432 failures (431 certificate
generation, one term decoding); combined reconstruction has 16 (11 certificate
generation and core-guided reconstruction, two heartbeat limits, three tactic
failures).

The implementation-effort table is computed from Lean source, not this archive.
Run `python3 scripts/count_replay_effort.py` from the repository root. The paper
reports 55 handlers, 256 handler LoC, and 797 supporting lemma LoC.

## Render the reference data

From the repository root, with the plotting dependencies installed (included in
the evaluation Docker image):

```bash
bash scripts/render-paper-artifacts.sh BenchmarkResults/reference-figures
```

The renderer unpacks the bundled archive automatically. See the top-level
[evaluation README](../../README.md) for the output-to-paper correspondence.

To regenerate reports and plots from an unpacked copy, without measuring any VCs:

```bash
mkdir -p BenchmarkResults/reference-data
unzip -q scripts/benchmark-data/eval-data.zip -d BenchmarkResults/reference-data
bash run-experiments.sh --figures_only BenchmarkResults/reference-data
```

`PAPER_DATA_ARCHIVE` selects another archive for the renderer;
`MEASUREMENTS_ROOT` selects a directory containing unpacked measurement groups.
Keep fresh-run outputs separate from this reference archive.

## Provenance and scope

This snapshot combines the paper's saved Curated, Cashmere, and Velvet
measurements with its PLean shared-scaffolding run from October 12–13, 2026.
The raw measurements and profiler events are preserved unchanged. It does not
substitute measurements from the later October 15 reproduction. Historical
metadata, where present, retains the recorded revisions, settings, and local
paths; these paths are provenance, not required inputs to rendering.

The benchmark scripts' dependency pins are documented in the
[script guide](../README.md). A fresh run uses those scripts to measure VCs;
the reference outcomes and timings are not used to fill in fresh results.
Runtime varies with hardware and system load, and timeout-sensitive outcomes
can vary between runs. Rendering this saved snapshot reproduces the paper's
reported numbers without that measurement variability.
