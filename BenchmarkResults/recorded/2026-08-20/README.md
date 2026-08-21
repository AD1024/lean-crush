# Recorded Benchmark Results

This snapshot preserves benchmark inputs used by the paper. Build logs, tactic
logs, source clones, and temporary worktrees are excluded.

## Paper Data

All canonical inputs for the current tables and figures are under
[`scripts/benchmark-data`](../../../scripts/benchmark-data). Regenerate every
artifact from that one directory with:

```sh
scripts/render-paper-artifacts.sh
```

The benchmark-data README documents the two measurements, their workloads, and
direct plotting commands.

## Earlier Runs

The `baselines/` directories preserve the superseded 2026-08-14 and
2026-08-15 inputs:

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
`eeecec410864b3f0d8f59b5555b0996f5478d701`. They remain available for
historical validation but are not inputs to the current headline table.
