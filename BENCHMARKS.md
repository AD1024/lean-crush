# Benchmarks

Auto and Duper results were measured on 2026-08-14. Crush was remeasured on
2026-08-15 from the reviewed working tree based on lean-crush commit
`eeecec410864b3f0d8f59b5555b0996f5478d701`. The comparison covers lean-auto,
Duper, and Crush across LeanHammer, Loom, Cashmere, Velvet, and PLean.

## Results

| Corpus | Backend | Solved / total | Coverage | Total (s) | Avg (ms) | Min (ms) | Max (ms) |
|---|---|---:|---:|---:|---:|---:|---:|
| LeanHammer, direct | Auto + Duper | 8 / 20 | 40.0% | 2.173 | 108.7 | 1.0 | 254.0 |
| LeanHammer, direct | Duper | 12 / 20 | 60.0% | 19.108 | 955.4 | 53.0 | 14,782.0 |
| **LeanHammer, direct** | **Crush** | **20 / 20** | **100.0%** | **0.820** | **41.0** | **5.0** | **131.0** |
| LeanHammer, Aesop portfolio | Aesop + Auto/Duper | 14 / 20 | 70.0% | 131.225 | 6,561.2 | 2.0 | 113,766.0 |
| **LeanHammer, Aesop portfolio** | **Aesop + Crush** | **20 / 20** | **100.0%** | **1.114** | **55.7** | **12.0** | **169.0** |
| **Loom** | **auto** | **4 / 4** | **100.0%** | **0.352** | **88.0** | **45.0** | **178.0** |
| Loom | Duper | 1 / 4 | 25.0% | 0.492 | 123.0 | 39.0 | 173.0 |
| Loom | Crush | 4 / 4 | 100.0% | 0.454 | 113.5 | 97.0 | 140.0 |
| Cashmere | auto | 18 / 38 | 47.4% | 5.232 | 137.7 | 2.0 | 211.0 |
| Cashmere | Duper | 21 / 38 | 55.3% | 46.526 | 1,224.4 | 1.0 | 12,280.0 |
| **Cashmere** | **Crush** | **38 / 38** | **100.0%** | **6.899** | **181.6** | **1.0** | **1,348.0** |
| Velvet, shared VCs | auto | 276 / 347 | 79.5% | 462.462 | 1,332.7 | 11.0 | 78,273.0 |
| Velvet, shared VCs | Duper | 193 / 347 | 55.6% | 1,444.073 | 4,161.6 | 0.0 | 270,961.0 |
| **Velvet, shared VCs** | **Crush** | **327 / 347** | **94.2%** | **156.433** | **450.8** | **1.0** | **17,510.0** |
| PLean | auto | 168 / 192 | 87.5% | 715.812 | 3,728.2 | 0.0 | 66,114.0 |
| **PLean** | **Crush** | **174 / 192** | **90.6%** | **3,229.188** | **16,818.7** | **0.0** | **733,365.0** |
| PLean, bounded stress | Duper | 19 / 30 | 63.3% | 43.176 | 1,439.2 | 0.0 | 4,963.3 |

**Rows.** `Duper` means direct proof-producing `duper [*]` after the host
project's normal VC preprocessing. LeanHammer's `Auto + Duper` lane is
LeanHammer's Auto translation and monomorphization pipeline feeding Duper, not
a sequential fallback. The Aesop rows race the named backend with Aesop.

Loom is a four-VC regression fixture. Cashmere contains all generated VCs in
its two case-study files. Velvet uses the 347 goal identities emitted by all
three tested branches, so every Velvet row measures the same obligations.
PLean contains the nine complete examples listed below, with registered manual
proofs disabled and incomplete `Paxos.lean` excluded.

PLean's bounded Duper stress row includes the 30 VCs in the four files that
completed under the configured per-file CPU limit. Five other files reached
that limit before reporting a complete VC set. They are marked in the
per-file table and excluded from the stress row's denominator and timings, so
that row is not directly comparable with the full 192-VC auto and Crush rows.

**Columns.** A VC is one Lean goal handed to the selected backend after host
preprocessing. `Solved / total` counts closed goals over attempted goals.
`Total` sums tactic-local time for all attempts; `Avg` divides it by attempted
VCs. `Min` and `Max` are individual attempt times. Total is in seconds and the
other timing columns are in milliseconds. The best row in each comparable
group is bold, comparing coverage first and average time when coverage ties.

These are not file or process wall times. Each VC was measured once, so timings
are regression indicators rather than stable microbenchmarks. LeanHammer
excludes its import-only case.

The latest PLean run preserved the previous result for every VC, but its
tactic-local counters had non-repeatable long tails. Its total file wall time
was 2,035 seconds, versus 2,289 seconds in the preceding checkpoint run. A
focused `TwoPhaseCommit` rerun took 378 seconds wall time versus 402 seconds at
the checkpoint. The table reports the latest full-run counters, but they should
not be interpreted as a repeatable performance regression.

The raw Velvet branches emitted 495 auto records, 483 Duper records, and 433
Crush records. Duper was truncated in `Examples_Total.lean` and
`Total_Partial_example.lean`; Crush was truncated in
`SpMSpV_Example.lean` and `SubstringSearch.lean`. The headline table uses the
latest 347-VC three-way intersection. The eight previously matched
`SubstringSearch` identities omitted by the latest run are declaration-level
heartbeat truncation, not newly failed VCs. Pairwise intersections below can
therefore be larger.

The 2026-08-15 validation reran the Crush lanes only. The matched rows join
those records to the unchanged pinned Auto and Duper records using the same
goal-identity keys as the harness.

## Matched VCs

| Corpus | Left | Right | Shared | Left only | Right only | Both | Neither | Left avg (ms) | Right avg (ms) |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| LeanHammer, direct | Auto + Duper | Duper | 20 | 0 | 4 | 8 | 8 | 162.0 | 93.0 |
| LeanHammer, direct | Duper | Crush | 20 | 0 | 8 | 12 | 0 | 115.1 | 31.1 |
| LeanHammer, direct | Auto + Duper | Crush | 20 | 0 | 12 | 8 | 0 | 162.0 | 24.0 |
| LeanHammer, Aesop | Aesop + Auto/Duper | Aesop + Crush | 20 | 0 | 6 | 14 | 0 | 107.1 | 40.6 |
| Loom | auto | Duper | 4 | 3 | 0 | 1 | 0 | 45.0 | 39.0 |
| Loom | Duper | Crush | 4 | 0 | 3 | 1 | 0 | 39.0 | 98.0 |
| Loom | auto | Crush | 4 | 0 | 0 | 4 | 0 | 88.0 | 113.5 |
| Cashmere | auto | Duper | 38 | 4 | 7 | 14 | 13 | 99.6 | 65.2 |
| Cashmere | Duper | Crush | 38 | 0 | 17 | 21 | 0 | 669.9 | 86.3 |
| Cashmere | auto | Crush | 38 | 0 | 20 | 18 | 0 | 109.2 | 67.3 |
| Velvet | auto | Duper | 394 | 132 | 34 | 186 | 42 | 730.9 | 964.0 |
| Velvet | Duper | Crush | 353 | 2 | 137 | 193 | 21 | 913.3 | 39.9 |
| Velvet | auto | Crush | 372 | 5 | 56 | 296 | 15 | 509.7 | 122.8 |
| PLean | auto | Duper | 30 | 11 | 0 | 19 | 0 | 483.4 | 1,289.1 |
| PLean | Duper | Crush | 30 | 0 | 11 | 19 | 0 | 1,289.1 | 145.6 |
| PLean | auto | Crush | 192 | 0 | 6 | 168 | 18 | 2,728.1 | 4,639.3 |

**Rows.** Each row compares two backends on obligations matched by case name
for LeanHammer, by file/proof/goal identity for Loom, Cashmere, and Velvet, or
by file/obligation name for PLean. The PLean comparisons involving Duper use
only the 30 VCs in files that completed its bounded stress run.

**Columns.** `Shared` is the number attempted by both backends. `Left only`,
`Right only`, `Both`, and `Neither` are disjoint outcomes summing to `Shared`.
The two averages include only `Both` goals, so they exclude failures and goals
solved by only one backend.

## PLean Files

| PLean example | Auto solved | Duper stress | Crush solved | Total |
|---|---:|---:|---:|---:|
| ClockBound | 56 | CPU limit | 56 | 56 |
| Consensus | 12 | CPU limit | 14 | 17 |
| DistributedLock | 12 | 8 | 12 | 12 |
| LockServer | 34 | CPU limit | 34 | 37 |
| PingPongAuto | 6 | 4 | 6 | 6 |
| PingPongTrivial | 1 | 1 | 1 | 1 |
| RingLeader | 11 | CPU limit | 11 | 14 |
| ShardedKV | 11 | 6 | 11 | 11 |
| TwoPhaseCommit | 25 | CPU limit | 29 | 38 |

**Rows.** Each row is one complete module under `Examples/`. `Total` is the
common number of generated VCs, not a sum of solved columns.

**Columns.** Backend columns count closed VCs only when a file completed.
`CPU limit` means that the file's Lean process reached its 60 CPU-second bound,
so no partial result is presented as complete coverage. Every file is run in a
separate process, so one limited file does not prevent later files from running.

## Configuration

Loom, Cashmere, and Velvet used cvc5 1.3.4 for auto and Crush, a five-second
solver timeout, one million Lean heartbeats per VC, and
`crush.trust = "reconstruct"`. Their Duper lane used a five-second saturation
limit and the same heartbeat cap. LeanHammer used its five-second portfolio
limits; raw Duper and Crush both produced checked Lean proofs.

PLean auto and Crush used cvc5, a five-second timeout, one million heartbeats,
disabled the proof cache and ground-instantiation fuel, and used
`crush.trust = "trust"` to match lean-auto's trusted SMT discharge. The
PLean Duper stress lane used one-second saturation, 20,000 heartbeats per VC,
and a 60 CPU-second limit per generated Lean file. This lower bounded
configuration was necessary because `ClockBound` exceeded 40 minutes at one
million heartbeats and 18 minutes at 200,000 heartbeats.

The machine was Apple Silicon arm64 running macOS 26.6, with Z3 4.15.4 and
cvc5 1.3.4. Duper was pinned at
`ca7c5862bee2e62e019e6a1b70ce95612b6b6365`. Builds and imports are excluded
from tactic-local times.

| Component | Auto revision | Duper revision | Crush revision | Lean |
|---|---|---|---|---|
| lean-crush | - | - | `eeecec410864b3f0d8f59b5555b0996f5478d701` + reviewed working tree | 4.32.2 |
| LeanHammer | `df4dd13671412591d678eada250b04c030fd4d40` | same tree | same tree | 4.32.2 |
| Loom and Cashmere | `78928abc9054b31d0bea85985496490baae95244` | `616f9cd8db660dcd74a1c92b0d19bb50420e1c59` | `ec16b95ff8bbd047248de031cabd3160847e4b1b` | 4.24.0 / 4.32.2 / 4.32.2 |
| Velvet | `d254391d5e84546f96576e5b67dfb6bafe9fc301` | `5a1180338958908323a921255a8d158cf1f26c95` | `e90d79341bb8ef510ec868623e74cfe98feaa4e8` | 4.24.0 / 4.32.2 / 4.32.2 |
| PLean | `be39726723e71f9aa1e02c6cfeeae9b0c31b8947` | `3557f1f0fa5246ee88fcde3776f3973349049968` | `9c098b4c5ad32faf2a022929b6726d2a182a9e1d` | 4.24.0 / 4.32.2 / 4.32.2 |

`same tree` means the profiles used the exact checkout. Loom supplies both the
Loom fixture and Cashmere integration. The Lean version order is auto, Duper,
then Crush.

## Reproduction

The corpus harness provisions and builds all pinned revisions:

```sh
REPEATS=1 \
TIMEOUT=5 \
DUPER_TIMEOUT=5 \
SOLVER=cvc5 \
CRUSH_TRUST=reconstruct \
MAX_HEARTBEATS=1000000 \
OUT_DIR="$PWD/BenchmarkResults/corpora-reproduction" \
scripts/benchmark-corpora.sh
```

The PLean harness runs all three published lanes with:

```sh
RUN_DUPER=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
CRUSH_TRUST=trust \
CRUSH_INST_FUEL=0 \
DUPER_TIMEOUT=1 \
DUPER_MAX_HEARTBEATS=20000 \
DUPER_FILE_CPU_SECONDS=60 \
OUT_DIR="$PWD/BenchmarkResults/plean-reproduction" \
scripts/benchmark-plean.sh
```

Each harness writes metadata, per-VC results, aggregate summaries, per-file
runs, and complete logs under `BenchmarkResults/`. A full corpus run writes the
headline intersection to `matched-summary.tsv`; Crush-only validation records
can be joined to pinned baseline records with the same key used by that report.
LeanHammer profiles come from `leanhammer/summary.tsv`, and PLean rows from
`summary.tsv` and `file-summary.tsv`. The bounded corpus command reports known
Velvet truncation after writing these files. Use `REPEATS=3` or more for
performance claims on lanes that complete.
