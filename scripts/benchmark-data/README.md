# Paper Artifact Data

This directory contains every machine-readable input used to draw the published
benchmark tables and figures. It is split into two internally consistent
measurements because the latest all-backend comparison and the earlier
reconstruction study use different Velvet workloads.

| Directory | Measurement |
|---|---|
| `main/` | Fixed-workload Auto, Duper, trusted Crush, and `grind` comparison |
| `crush-modes/` | Trusted verification, Core, Alethe, and portfolio reconstruction |

Each measurement has `corpora`, `leanhammer`, and `plean` directories containing
normalized TSV reports. The per-VC measurements and profiler events needed to
audit or regenerate those reports are retained alongside them.

From the repository root, redraw all paper tables and figures into
`BenchmarkResults/figures` with:

```sh
scripts/render-paper-artifacts.sh
```

Pass a different output directory as the first argument:

```sh
scripts/render-paper-artifacts.sh /tmp/lean-crush-paper-artifacts
```

The renderer uses only Python's standard library. It rejects conflicting
aggregate rows, inconsistent corpus totals, and incomplete outcome partitions.
The benchmark reporter generated the retained main inputs with
`--require-uniform-headline`, which separately verified exact VC identities.

The `main` comparison uses trusted Crush (`crush.trust = "trust"`). Its
LeanHammer and PLean directories combine baseline measurements with retained
trusted-Crush measurements only after exact VC-identity validation. The
corpus and LeanHammer trusted-Crush lanes use lean-crush commit
`dac5f9357388a7ee5bb81501410866ec3fa14038`; PLean reuses the trusted lane from
the reconstruction run. The `crush-modes` measurement uses lean-crush commit
`08a4eb091e94a369dc8eb77b70cacffe7f0138ff`; exact downstream revisions and
options are in each measurement's metadata.
