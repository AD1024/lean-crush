# Benchmarks

Crush and `grind` were measured on 2026-08-20 from clean lean-crush commit
`08a4eb091e94a369dc8eb77b70cacffe7f0138ff`. The current measurement separates
trusted SMT verification from Core, Alethe, and portfolio reconstruction.
Auto and Duper were not rerun; their 2026-08-14 comparison is retained in
[Historical Backend Comparison](#historical-backend-comparison).

The [Verso benchmark chapter](https://ad1024.github.io/lean-crush/Benchmarks/)
publishes the figures. The exact reproduction commands and output schemas are
in [`scripts/README.md`](scripts/README.md).

## Current Coverage

| Corpus | Lane | Solved / attempted | Coverage | Total (s) | Avg (ms) |
|---|---|---:|---:|---:|---:|
| **LeanHammer** | **Crush, Z3 checked** | **20 / 20** | **100.0%** | **0.863** | **43.2** |
| LeanHammer | Crush verify | 19 / 20 | 95.0% | 6.113 | 305.7 |
| LeanHammer | Core | 19 / 20 | 95.0% | 6.056 | 302.8 |
| LeanHammer | Alethe | 13 / 20 | 65.0% | 14.063 | 703.2 |
| LeanHammer | Portfolio | 19 / 20 | 95.0% | 9.833 | 491.7 |
| LeanHammer | `grind` | 16 / 20 | 80.0% | 0.067 | 3.4 |
| Loom | Crush verify | 4 / 4 | 100.0% | 0.360 | 90.0 |
| Loom | Core | 4 / 4 | 100.0% | 0.335 | 83.8 |
| Loom | Alethe | 4 / 4 | 100.0% | 12.660 | 3,165.0 |
| Loom | Portfolio | 4 / 4 | 100.0% | 12.797 | 3,199.3 |
| **Loom** | **`grind`** | **4 / 4** | **100.0%** | **0.036** | **9.0** |
| **Cashmere** | **Crush verify** | **38 / 38** | **100.0%** | **6.769** | **178.1** |
| Cashmere | Core | 38 / 38 | 100.0% | 6.947 | 182.8 |
| Cashmere | Alethe | 9 / 38 | 23.7% | 7.249 | 190.8 |
| Cashmere | Portfolio | 38 / 38 | 100.0% | 6.825 | 179.6 |
| Cashmere | `grind` | 19 / 38 | 50.0% | 0.274 | 7.2 |
| **Velvet** | **Crush verify** | **406 / 425** | **95.5%** | **213.187** | **415.6** |
| Velvet | Core | 355 / 378 | 93.9% | 295.341 | 682.1 |
| Velvet | Alethe | 133 / 425 | 31.3% | 235.784 | 459.6 |
| Velvet | Portfolio | 355 / 378 | 93.9% | 316.181 | 730.2 |
| Velvet | `grind` | 369 / 425 | 86.8% | 28.264 | 55.1 |
| **PLean** | **Crush verify** | **174 / 192** | **90.6%** | **1,378.833** | **7,181.4** |
| PLean | Core | 161 / 192 | 83.9% | 47,552.983 | 247,671.8 |
| PLean | Alethe | 8 / 192 | 4.2% | 550.113 | 2,865.2 |
| PLean | Portfolio | 161 / 192 | 83.9% | 45,540.817 | 237,191.8 |
| PLean | `grind` | 174 / 192 | 90.6% | 2,703.132 | 14,078.8 |

**Rows.** `Crush verify` uses `crush.trust = "trust"` and measures collection,
translation, and SMT solving without requiring a checked reconstruction.
`Core` and `Alethe` are strict checked lanes. `Portfolio` tries Alethe first,
then Core. The LeanHammer Z3 row is the existing checked `crush-only` profile;
the other Crush rows use cvc5. `grind` receives the same host-generated VCs.

**Columns.** `Solved / attempted` counts unique VC identities closed by that
lane. `Total` sums tactic-local attempt time and `Avg` divides by attempts.
PLean elaborates declarations concurrently, so its tactic-local totals overlap;
the corresponding sums of per-file wall time are 1,170 seconds for verify,
3,016 for Core, 1,280 for Alethe, 2,802 for Portfolio, and 2,342 for `grind`.
Bold rows compare coverage first and average time when coverage ties. Different
lanes provide different trust guarantees, so speed alone is not an
interchangeable proof-quality comparison.

Velvet Core and Portfolio attempted 378 rather than 425 VCs because an earlier
failure or declaration heartbeat stopped some generated files. Their raw lane
coverage uses 378 as its denominator. The reconstruction table below instead
uses the common set verified by the trusted lane.

## Reconstruction Coverage

| Corpus | SMT verified / total | Core / verified | Alethe / verified | Portfolio / verified |
|---|---:|---:|---:|---:|
| LeanHammer | 19 / 20 | **19 / 19** | 13 / 19 | **19 / 19** |
| Loom | 4 / 4 | **4 / 4** | **4 / 4** | **4 / 4** |
| Cashmere | 38 / 38 | **38 / 38** | 9 / 38 | **38 / 38** |
| Velvet | 406 / 425 | **355 / 406** | 133 / 406 | **355 / 406** |
| PLean | 174 / 192 | **157 / 174** | 1 / 174 | **157 / 174** |

The denominator for all three checked columns is the VC set solved by
`Crush verify`. A checked lane also counts goals closed by a selected Lean fact
or pre-reconstruction before SMT, because those already produce a
kernel-checked proof. `alethe-replay-scaling.tsv` separately includes only
successful certificate replays.

## Reconstruction Gaps

| Corpus | Lane | Failure mode | Verified VCs |
|---|---|---|---:|
| LeanHammer | Alethe | certificate error | 2 |
| LeanHammer | Alethe | assumption/rule gap | 1 |
| LeanHammer | Alethe | term decoder gap | 1 |
| LeanHammer | Alethe | solver `sat` | 1 |
| LeanHammer | Alethe | solver `unknown` | 1 |
| Cashmere | Alethe | certificate error | 29 |
| Velvet | Core | reconstruction failed | 4 |
| Velvet | Core | not attempted after file termination | 47 |
| Velvet | Alethe | certificate error | 230 |
| Velvet | Alethe | assumption/rule gap | 26 |
| Velvet | Alethe | term decoder gap | 14 |
| Velvet | Alethe | solver `unknown` | 3 |
| Velvet | Portfolio | Alethe certificate error + Core failed | 4 |
| Velvet | Portfolio | not attempted after file termination | 47 |
| PLean | Core | reconstruction failed | 6 |
| PLean | Core | solver `unknown` | 4 |
| PLean | Core | host tactic failed | 7 |
| PLean | Alethe | certificate error | 173 |
| PLean | Portfolio | Alethe certificate error + Core failed | 6 |
| PLean | Portfolio | solver `unknown` | 4 |
| PLean | Portfolio | host tactic failed | 7 |

Rows partition verified VCs not closed by the named strict lane.
`not attempted` is not a reconstruction failure: the generated Velvet file
terminated before reaching that VC. Every recorded certificate error in this
run is cvc5 rejecting proof output containing `DUMMY_SKOLEM`. Rule and term
gaps are replay coverage limitations. Solver `sat` and `unknown` occur before
replay. Portfolio failures report the final Core outcome after Alethe failed.

## Phase Timing

| Corpus | Lane | Accounted (s) | Largest profiler phases |
|---|---|---:|---|
| LeanHammer | Verify | 6.073 | solve 96.8%, translate 1.5% |
| LeanHammer | Core | 6.005 | solve 94.3%, reconstruct 2.9% |
| LeanHammer | Alethe | 13.991 | replay 55.0%, solve 43.7% |
| LeanHammer | Portfolio | 9.787 | solve 56.5%, replay 41.3% |
| Loom | Verify | 0.341 | solve 92.2%, translate 3.9% |
| Loom | Core | 0.313 | solve 71.1%, reconstruct 22.1% |
| Loom | Alethe | 12.631 | replay 98.1%, solve 1.8% |
| Loom | Portfolio | 12.766 | replay 97.7%, solve 2.2% |
| Cashmere | Verify | 6.577 | instantiate 60.5%, pre-reconstruct 18.4%, solve 14.3% |
| Cashmere | Core | 6.781 | instantiate 45.1%, pre-reconstruct 22.3%, reconstruct 15.9% |
| Cashmere | Alethe | 7.073 | instantiate 77.2%, solve 15.2%, translate 6.8% |
| Cashmere | Portfolio | 6.657 | instantiate 46.4%, pre-reconstruct 22.3%, reconstruct 15.9% |
| Velvet | Verify | 204.154 | solve 74.4%, fallback solve 10.0%, instantiate 6.5% |
| Velvet | Core | 291.053 | solve 43.8%, reconstruct 40.2%, fallback solve 7.0% |
| Velvet | Alethe | 231.131 | solve 66.2%, replay 15.3%, fallback solve 8.8% |
| Velvet | Portfolio | 311.887 | solve 40.4%, reconstruct 36.0%, replay 8.7% |
| PLean | Verify | 2,348.973 | solve 54.2%, pre-reconstruct 43.1%, translate 2.2% |
| PLean | Core | 55,830.332 | reconstruct 68.0%, pre-reconstruct 29.9%, solve 2.0% |
| PLean | Alethe | 828.350 | solve 79.1%, translate 17.1%, normalize 3.6% |
| PLean | Portfolio | 53,482.310 | reconstruct 67.8%, pre-reconstruct 30.1%, solve 2.1% |

`Accounted` sums profiler events, not process wall time. One host VC may invoke
Crush more than once, and PLean declarations elaborate concurrently. The
machine-readable `phase-summary.tsv` records event count, total, mean, minimum,
maximum, and percentage for every phase; the
[stacked figure](https://ad1024.github.io/lean-crush/Benchmarks/Time-Breakdown/)
shows the complete distribution.

## Alethe Scaling

| Corpus | Replayed VCs | Commands | Replay time (ms) | Pearson r | R-squared | ms / 100 commands |
|---|---:|---:|---:|---:|---:|---:|
| LeanHammer | 13 | 3-231 | 5.986-4,731.513 | 0.8610 | 0.7413 | 1,534.658 |
| Loom | 4 | 14-673 | 79.693-8,461.178 | 0.9528 | 0.9078 | 1,114.326 |
| Velvet | 26 | 10-275 | 27.115-7,132.694 | 0.7936 | 0.6298 | 1,579.287 |

Each point is one successful strict Alethe replay, averaged by VC across
repeats. Script length is the parsed Alethe command count. Replay time includes
certificate parsing, step replay, proof assembly, and final kernel checking,
but excludes solver time. Cashmere and PLean have no successful certificate
replay samples; their strict-lane successes closed before replay.

## Current Configuration

All current cvc5 lanes used cvc5 1.3.4, Lean 4.32.2, a five-second
per-query timeout, one million heartbeats per VC, and
`maxRecDepth = 1000000`. PLean additionally disabled ground-instantiation fuel.
The machine was Apple Silicon arm64 running macOS 26.6; the LeanHammer Z3 lane
used Z3 4.15.4.

| Component | Revision |
|---|---|
| lean-crush | `08a4eb091e94a369dc8eb77b70cacffe7f0138ff` |
| LeanHammer | `df4dd13671412591d678eada250b04c030fd4d40` |
| Loom and Cashmere | `ec16b95ff8bbd047248de031cabd3160847e4b1b` |
| Velvet | `e90d79341bb8ef510ec868623e74cfe98feaa4e8` |
| PLean | `9c098b4c5ad32faf2a022929b6726d2a182a9e1d` |

## Historical Backend Comparison

Auto and Duper results below were measured on 2026-08-14. Crush was remeasured
on 2026-08-15 from the reviewed working tree based on lean-crush commit
`eeecec410864b3f0d8f59b5555b0996f5478d701`. These rows are retained for the
cross-backend comparison and are separate from the current reconstruction
measurement above.

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

## Historical Configuration

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

Reproduce the current Crush and `grind` corpus lanes:

```sh
RUN_AUTO=false \
RUN_DUPER=false \
REPEATS=1 \
TIMEOUT=5 \
SOLVER=cvc5 \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
OUT_DIR="$PWD/BenchmarkResults/corpora-reproduction" \
scripts/benchmark-corpora.sh
```

Reproduce LeanHammer:

```sh
REPEATS=1 \
MAX_RECURSION_DEPTH=1000000 \
OUT_DIR="$PWD/BenchmarkResults/leanhammer-reproduction" \
scripts/benchmark-leanhammer.sh
```

Reproduce PLean without incomplete `Paxos.lean`:

```sh
RUN_AUTO=false \
RUN_DUPER=false \
RUN_CRUSH=true \
RUN_GRIND=true \
REPEATS=1 \
SOLVER=cvc5 \
TIMEOUT=5 \
MAX_HEARTBEATS=1000000 \
MAX_RECURSION_DEPTH=1000000 \
CRUSH_INST_FUEL=0 \
OUT_DIR="$PWD/BenchmarkResults/plean-reproduction" \
scripts/benchmark-plean.sh
```

Render the tables and the SVGs used by the Verso manual:

```sh
python3 scripts/plot-benchmarks.py \
  BenchmarkResults/corpora-reproduction \
  BenchmarkResults/leanhammer-reproduction \
  BenchmarkResults/plean-reproduction \
  --out-dir Doc/Verso/figures \
  --skip-tables
```

Each harness writes metadata, per-VC measurements, profiler events, coverage,
reconstruction, failure, phase, and Alethe-scaling reports, plus complete logs.
The bounded corpus command reports known Velvet truncation after writing its
valid reports. Use `REPEATS=3` or more for performance claims on lanes that
complete. Commands for historical Auto and Duper lanes are in
[`scripts/README.md`](scripts/README.md).
