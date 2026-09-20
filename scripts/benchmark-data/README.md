# Paper Artifact Data

`eval-data.zip` holds every machine-readable input behind the benchmark tables
and figures. One archive rather than several hundred loose TSVs, so refreshing a
measurement is a single binary change instead of a repo-wide add and delete.

| Directory in the archive | Measurement |
|---|---|
| `main/` | Coverage comparison: Auto, Duper, lean-smt, trusted Crush, kernel-checked Crush, `grind` |
| `crush-modes/` | Crush's own lanes: trusted verification, strict Alethe replay, portfolio |
| `reconstruction/` | Cross-tool: lean-smt beside Crush's Alethe and portfolio lanes |

Each holds `corpora/`, `leanhammer/` and `plean/` with normalized TSV reports,
per-VC measurements, and profiler events. `corpora/` carries Cashmere and Velvet
together, distinguished by the `suite` column; `main/` also retains Loom's four
historical VCs, which the paper renderer excludes.

The three studies cover the same 754 paper VC identities: LeanHammer (20),
Cashmere (38), Velvet (504), PLean (192).

## Reading it

The renderer unpacks the archive itself:

```sh
bash scripts/render-paper-artifacts.sh
```

To inspect the data directly, or to render from loose directories:

```sh
mkdir -p /tmp/eval && unzip -q scripts/benchmark-data/eval-data.zip -d /tmp/eval
PAPER_DATA_ROOT=/tmp/eval bash scripts/render-paper-artifacts.sh
```

`MAIN_ROOT`, `MODES_ROOT`, and `RECONSTRUCTION_ROOT` override one study each,
which is how a fresh run is drawn without touching the archive. See the
[script guide](../README.md) for the harnesses that produce these runs and for
rebuilding the archive from one.

## Provenance

Every row records its own origin. `metadata.tsv` in each suite directory names
the corpus revision, toolchain, solver, timeout, the lean-crush commit, and
whether its working tree was dirty. A suite measured in more than one run keeps
one row per run.

Timings are only comparable within a single run on a single host: the external
solver call is the part that moves most, and VCs near the 5s cvc5 cap can flip
between runs on the same machine. Coverage reproduces; times do not.
