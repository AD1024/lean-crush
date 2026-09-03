# Benchmarks

The headline comparison evaluates Auto, Duper, trusted Crush, and `grind` on
one fixed set of verification-condition identities per corpus. Trusted Crush
uses `crush.trust = "trust"` and measures collection, specialization,
translation, and SMT solving without proof reconstruction. Checked
reconstruction is measured separately below.

The [Verso benchmark chapter](https://ad1024.github.io/lean-crush/Benchmarks/)
publishes the figures. Machine-readable inputs are retained under
[`scripts/benchmark-data`](scripts/benchmark-data),
and [`scripts/README.md`](scripts/README.md#paper-artifacts) gives
self-contained reproduction commands.
The values below are the latest normalized comparison in
`scripts/benchmark-data/main`;
run `scripts/render-paper-artifacts.sh` to regenerate the machine-derived table
and figures.

## Main Comparison

| Corpus | Backend | Solved / total | Coverage | Total (s) | Avg (ms) | Min (ms) | Max (ms) |
|---|---|---:|---:|---:|---:|---:|---:|
| LeanHammer | Auto | 8 / 20 | 40.0% | 3.240 | 162.0 | 2.0 | 1,317.0 |
| LeanHammer | Duper | 12 / 20 | 60.0% | 19.348 | 967.4 | 43.0 | 15,745.0 |
| **LeanHammer** | **Crush** | **19 / 20** | **95.0%** | **6.133** | **306.7** | **2.0** | **5,070.0** |
| LeanHammer | `grind` | 16 / 20 | 80.0% | 0.074 | 3.7 | 0.0 | 13.0 |
| Loom | Auto | 4 / 4 | 100.0% | 0.974 | 243.5 | 44.0 | 607.0 |
| Loom | Duper | 1 / 4 | 25.0% | 0.454 | 113.5 | 36.0 | 174.0 |
| Loom | Crush | 4 / 4 | 100.0% | 0.418 | 104.5 | 53.0 | 139.0 |
| **Loom** | **`grind`** | **4 / 4** | **100.0%** | **0.048** | **12.0** | **7.0** | **17.0** |
| Cashmere | Auto | 18 / 38 | 47.4% | 5.379 | 141.6 | 2.0 | 631.0 |
| Cashmere | Duper | 21 / 38 | 55.3% | 65.087 | 1,712.8 | 1.0 | 40,739.0 |
| **Cashmere** | **Crush** | **38 / 38** | **100.0%** | **6.307** | **166.0** | **1.0** | **566.0** |
| Cashmere | `grind` | 19 / 38 | 50.0% | 0.289 | 7.6 | 4.0 | 13.0 |
| Velvet | Auto | 415 / 504 | 82.3% | 344.974 | 684.5 | 11.0 | 12,866.0 |
| Velvet | Duper | 292 / 504 | 57.9% | 1,039.652 | 2,062.8 | 0.0 | 15,077.0 |
| **Velvet** | **Crush** | **484 / 504** | **96.0%** | **171.406** | **340.1** | **0.0** | **10,386.0** |
| Velvet | `grind` | 444 / 504 | 88.1% | 21.409 | 42.5 | 0.0 | 3,000.0 |
| PLean | Auto | 168 / 192 | 87.5% | 301.027 | 1,567.9 | 0.0 | 17,280.7 |
| PLean | Duper | 71 / 192 | 37.0% | 81.281 | 423.3 | 0.0 | 2,174.6 |
| **PLean** | **Crush** | **174 / 192** | **90.6%** | **1,378.833** | **7,181.4** | **0.0** | **301,768.7** |
| PLean | `grind` | 155 / 192 | 80.7% | 76.005 | 395.9 | 0.0 | 3,859.6 |

`Auto` is the host project's lean-auto backend. In LeanHammer, its lane is the
Auto translation and monomorphization pipeline feeding Duper. `Duper` invokes
Duper directly after host preprocessing. PLean bounds Duper at one second of
saturation and 20,000 heartbeats per VC, but does not cap the generated file,
so all 192 VCs receive an attempt. `grind` is Lean's kernel-checked tactic.

Every backend has zero missing attempts. `Solved / total` therefore uses the
same denominator and exact VC identities within a corpus. `Total` sums
tactic-local attempt time; `Avg`, `Min`, and `Max` describe individual
attempts. Bold rows compare coverage first and average time when coverage ties.
The runs use one repeat, and some baseline and trusted-Crush lanes were
measured separately. Treat timings as reproducible regression measurements,
not statistically stable performance claims.

## Outcome Breakdown

| Corpus | Backend | Success | Translation error | Timeout | Failed to prove | Total |
|---|---|---:|---:|---:|---:|---:|
| LeanHammer | Auto | 8 | 1 | 0 | 11 | 20 |
| LeanHammer | Duper | 12 | 0 | 1 | 7 | 20 |
| LeanHammer | Crush | 19 | 0 | 1 | 0 | 20 |
| LeanHammer | `grind` | 16 | 0 | 0 | 4 | 20 |
| Loom | Auto | 4 | 0 | 0 | 0 | 4 |
| Loom | Duper | 1 | 0 | 0 | 3 | 4 |
| Loom | Crush | 4 | 0 | 0 | 0 | 4 |
| Loom | `grind` | 4 | 0 | 0 | 0 | 4 |
| Cashmere | Auto | 18 | 0 | 0 | 20 | 38 |
| Cashmere | Duper | 21 | 0 | 1 | 16 | 38 |
| Cashmere | Crush | 38 | 0 | 0 | 0 | 38 |
| Cashmere | `grind` | 19 | 0 | 0 | 19 | 38 |
| Velvet | Auto | 415 | 0 | 0 | 89 | 504 |
| Velvet | Duper | 292 | 0 | 133 | 79 | 504 |
| Velvet | Crush | 484 | 0 | 14 | 6 | 504 |
| Velvet | `grind` | 444 | 0 | 0 | 60 | 504 |
| PLean | Auto | 168 | 6 | 0 | 18 | 192 |
| PLean | Duper | 71 | 0 | 19 | 102 | 192 |
| PLean | Crush | 174 | 0 | 16 | 2 | 192 |
| PLean | `grind` | 155 | 0 | 0 | 37 | 192 |

The four outcome columns partition each backend's fixed workload. `Success`
means the VC was closed. `Translation error` requires an explicit unsupported
translation or encoding diagnostic. `Timeout` requires an explicit wall-clock,
heartbeat, or saturation-limit diagnostic. `Failed to prove` contains every
other unsuccessful attempt, including solver `sat` or ordinary `unknown`,
exhausted proof search, reconstruction failure, and other tactic errors.

## Aligned VCs

| Corpus | Baseline | Matched | Baseline only | Crush only | Both | Neither | Baseline avg (ms) | Crush avg (ms) |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| LeanHammer | Auto | 20 | 0 | 11 | 8 | 1 | 293.6 | 62.9 |
| LeanHammer | Duper | 20 | 1 | 8 | 11 | 0 | 76.9 | 59.3 |
| LeanHammer | `grind` | 20 | 0 | 3 | 16 | 1 | 4.4 | 56.8 |
| Loom | Auto | 4 | 0 | 0 | 4 | 0 | 243.5 | 104.5 |
| Loom | Duper | 4 | 0 | 3 | 1 | 0 | 36.0 | 53.0 |
| Loom | `grind` | 4 | 0 | 0 | 4 | 0 | 12.0 | 104.5 |
| Cashmere | Auto | 38 | 0 | 20 | 18 | 0 | 101.1 | 73.1 |
| Cashmere | Duper | 38 | 0 | 17 | 21 | 0 | 98.5 | 82.8 |
| Cashmere | `grind` | 38 | 0 | 19 | 19 | 0 | 7.2 | 69.4 |
| Velvet | Auto | 504 | 5 | 74 | 410 | 15 | 181.0 | 134.3 |
| Velvet | Duper | 504 | 2 | 194 | 290 | 18 | 210.8 | 60.2 |
| Velvet | `grind` | 504 | 6 | 46 | 438 | 14 | 20.9 | 101.6 |
| PLean | Auto | 192 | 0 | 6 | 168 | 18 | 885.8 | 2,181.4 |
| PLean | Duper | 192 | 0 | 103 | 71 | 18 | 428.3 | 225.2 |
| PLean | `grind` | 192 | 0 | 19 | 155 | 18 | 208.3 | 7,306.7 |

Each row compares trusted Crush with one baseline. `Matched` is the exact
VC-identity intersection. `Baseline only`, `Crush only`, `Both`, and `Neither`
partition that intersection. Timing averages include only `Both` VCs, so a
backend cannot appear faster by failing more goals. These rows do not compare
two baselines with each other.

## Reconstruction

The checked reconstruction measurement predates the final uniform headline
run. Its Velvet workload has 425 VCs rather than the expanded 504-VC headline
workload. It remains useful for comparing trusted verification, Core
reconstruction, strict Alethe replay, and the reconstruction portfolio on the
same recorded Crush inputs.

| Corpus | Verify solved / total | SMT cohort / verify solved | Core / SMT cohort | Alethe / SMT cohort | Portfolio / SMT cohort |
|---|---:|---:|---:|---:|---:|
| LeanHammer | 19 / 20 | 15 / 19 | 15 / 15 | 11 / 15 | 15 / 15 |
| Loom | 4 / 4 | 4 / 4 | 4 / 4 | 4 / 4 | 4 / 4 |
| Cashmere | 38 / 38 | 23 / 38 | 23 / 23 | 0 / 23 | 23 / 23 |
| Velvet | 406 / 425 | 263 / 406 | 225 / 263 | 24 / 263 | 225 / 263 |
| PLean | 174 / 192 | 172 / 174 | 155 / 172 | 0 / 172 | 155 / 172 |

`Verify solved` includes selected Lean facts and goals closed by checked pre-SMT
reconstruction. The reconstruction denominator is the narrower `SMT cohort`:
verify-lane successes whose profile records that SMT actually returned
`unsat`. This keeps pre-SMT closures out of certificate-reconstruction rates.

### Reconstruction Gaps

| Corpus | Lane | Failure mode | SMT-cohort VCs |
|---|---|---|---:|
| LeanHammer | Alethe | certificate error | 2 |
| LeanHammer | Alethe | assumption/rule gap | 1 |
| LeanHammer | Alethe | term decoder gap | 1 |
| Cashmere | Alethe | certificate error | 23 |
| Velvet | Core | reconstruction failed | 4 |
| Velvet | Core | not attempted after file termination | 34 |
| Velvet | Alethe | certificate error | 210 |
| Velvet | Alethe | assumption/rule gap | 21 |
| Velvet | Alethe | term decoder gap | 8 |
| Velvet | Portfolio | Alethe certificate error + Core failed | 4 |
| Velvet | Portfolio | not attempted after file termination | 34 |
| PLean | Core | reconstruction failed | 6 |
| PLean | Core | solver `unknown` | 4 |
| PLean | Core | host tactic failed | 7 |
| PLean | Alethe | certificate error | 172 |
| PLean | Portfolio | Alethe certificate error + Core failed | 6 |
| PLean | Portfolio | solver `unknown` | 4 |
| PLean | Portfolio | host tactic failed | 7 |

`not attempted` means an earlier declaration failure stopped the generated
file before the strict lane reached that VC; it is not a reconstruction
attempt. Certificate errors in this run are cvc5 proof-output failures
involving `DUMMY_SKOLEM`. Rule and term gaps are replay coverage limitations.

### Phase Timing

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

`Accounted` sums profiler events rather than process wall time. One host VC may
invoke Crush more than once. `phase-summary.tsv` records event count, total,
mean, minimum, maximum, and percentage for every phase.

### Alethe Scaling

| Corpus | Replayed VCs | Commands | Replay time (ms) | Pearson r | R-squared | ms / 100 commands |
|---|---:|---:|---:|---:|---:|---:|
| LeanHammer | 13 | 3-231 | 6.0-4,731.5 | 0.8610 | 0.7413 | 1,534.7 |
| Loom | 4 | 14-673 | 79.7-8,461.2 | 0.9528 | 0.9078 | 1,114.3 |
| Velvet | 26 | 10-275 | 27.1-7,132.7 | 0.7936 | 0.6298 | 1,579.3 |

Each point is one successful strict Alethe replay, averaged by VC across
repeats. Script length is the parsed Alethe command count. Replay time includes
certificate parsing, step replay, proof assembly, and final kernel checking,
but excludes solver time. Cashmere and PLean have no successful certificate
replay samples; their strict-lane successes closed before replay.

## Configuration

The main corpus and LeanHammer lanes use a five-second solver or saturation
limit and one million Lean heartbeats per VC. PLean uses the same Crush timeout
and heartbeat budget, disables Crush ground-instantiation fuel, and uses the
bounded Duper settings described above. Builds and imports are excluded from
tactic-local timing. The measurements were collected on Apple Silicon arm64
running macOS 26.6 with Z3 4.15.4 and cvc5 1.3.4.

| Component | Auto revision | Duper revision | Crush / `grind` revision |
|---|---|---|---|
| LeanHammer | `df4dd13671412591d678eada250b04c030fd4d40` | same tree | same tree |
| Loom and Cashmere | `78928abc9054b31d0bea85985496490baae95244` | `616f9cd8db660dcd74a1c92b0d19bb50420e1c59` | `ec16b95ff8bbd047248de031cabd3160847e4b1b` |
| Velvet | `d254391d5e84546f96576e5b67dfb6bafe9fc301` | `5a1180338958908323a921255a8d158cf1f26c95` | `e90d79341bb8ef510ec868623e74cfe98feaa4e8` |
| PLean | `be39726723e71f9aa1e02c6cfeeae9b0c31b8947` | `3557f1f0fa5246ee88fcde3776f3973349049968` | `9c098b4c5ad32faf2a022929b6726d2a182a9e1d` |

Duper is pinned at
`ca7c5862bee2e62e019e6a1b70ce95612b6b6365`. The PLean `grind` lane applies
the recorded pure-`grind` patch and guards against invoking an external
solver. Exact options, toolchains, dirty-state hashes, and per-file wall times
are in the recorded metadata and run files.

The reconstruction measurement uses lean-crush commit
`08a4eb091e94a369dc8eb77b70cacffe7f0138ff`. No implementation source under
`Crush/`, `Test/`, or `MathlibTest/` changed between that commit and the
headline harness checkpoints.
