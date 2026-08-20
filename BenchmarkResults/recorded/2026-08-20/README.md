# Recorded Benchmark Results, 2026-08-20

This snapshot preserves the machine-readable inputs for the figures and
benchmark comparisons published on 2026-08-20. Build logs, tactic logs, source
clones, and temporary worktrees are excluded.

## Figures

The `figures/` directories are byte-for-byte copies of every TSV in:

| Snapshot directory | Original result directory |
|---|---|
| `figures/corpora` | `BenchmarkResults/crush-measurement-20260820/corpora-final` |
| `figures/leanhammer` | `BenchmarkResults/crush-measurement-20260820/leanhammer-final` |
| `figures/plean` | `BenchmarkResults/crush-measurement-20260820/plean-final` |

Regenerate the published figures with:

```sh
python3 scripts/plot-benchmarks.py \
  BenchmarkResults/recorded/2026-08-20/figures/corpora \
  BenchmarkResults/recorded/2026-08-20/figures/leanhammer \
  BenchmarkResults/recorded/2026-08-20/figures/plean \
  --out-dir Doc/Verso/figures \
  --skip-tables
```

The runs use clean lean-crush commit
`08a4eb091e94a369dc8eb77b70cacffe7f0138ff`. Exact downstream revisions and
options are recorded in each `metadata.tsv`.

## Baselines

The `baselines/` directories preserve the TSV records behind the Auto, Duper,
and paired Crush rows in `BENCHMARKS.md`:

| Result directory | Published use |
|---|---|
| `full-20260814` | Auto corpus and LeanHammer baselines |
| `duper-comparison` | Direct LeanHammer Duper baseline |
| `duper-corpora` | Loom, Cashmere, and Velvet Duper baselines |
| `duper-plean-repro` | Bounded PLean Duper baseline |
| `plean-20260814-bounded` | PLean Auto baseline |
| `post-instance-corpora` | Paired Crush corpus comparison |
| `post-instance-leanhammer` | Paired Crush LeanHammer comparison |
| `post-instance-plean` | Paired Crush PLean comparison |
| `post-instance-plean-twophase-rerun` | PLean timing validation |
| `post-instance-substring-complete` | Velvet truncation validation |

Auto and Duper were measured on 2026-08-14. The paired Crush comparison was
measured on 2026-08-15 from a reviewed working tree based on
`eeecec410864b3f0d8f59b5555b0996f5478d701`. These records are intentionally
separate from the 2026-08-20 reconstruction measurement.
