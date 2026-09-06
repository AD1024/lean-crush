# Benchmarks

The headline comparison evaluates Auto, Duper, trusted Crush, and `grind` on
one fixed set of verification-condition identities per corpus. Trusted Crush
uses `crush.trust = "trust"` and measures collection, specialization,
translation, and SMT solving without proof reconstruction. Checked
reconstruction is measured separately below.

The harnesses also support [lean-smt](https://github.com/ufmg-smite/lean-smt)
as a fifth LeanHammer backend and as a third checked-reconstruction lane. The
main and reconstruction tables on this page predate that lane and contain no
lean-smt rows; its own measurement is in
[lean-smt](#lean-smt) below.

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
| LeanHammer | lean-smt | 12 / 20 | 60.0% | 1.873 | 93.7 | 50.0 | 144.0 |
| **LeanHammer** | **Crush** | **19 / 20** | **95.0%** | **6.133** | **306.7** | **2.0** | **5,070.0** |
| LeanHammer | `grind` | 16 / 20 | 80.0% | 0.074 | 3.7 | 0.0 | 13.0 |
| Loom | Auto | 4 / 4 | 100.0% | 0.974 | 243.5 | 44.0 | 607.0 |
| Loom | Duper | 1 / 4 | 25.0% | 0.454 | 113.5 | 36.0 | 174.0 |
| Loom | Crush | 4 / 4 | 100.0% | 0.418 | 104.5 | 53.0 | 139.0 |
| **Loom** | **`grind`** | **4 / 4** | **100.0%** | **0.048** | **12.0** | **7.0** | **17.0** |
| Cashmere | Auto | 18 / 38 | 47.4% | 5.379 | 141.6 | 2.0 | 631.0 |
| Cashmere | Duper | 21 / 38 | 55.3% | 65.087 | 1,712.8 | 1.0 | 40,739.0 |
| Cashmere | lean-smt | 17 / 38 | 44.7% | 5.547 | 146.0 | 41.0 | 244.0 |
| **Cashmere** | **Crush** | **38 / 38** | **100.0%** | **6.307** | **166.0** | **1.0** | **566.0** |
| Cashmere | `grind` | 19 / 38 | 50.0% | 0.289 | 7.6 | 4.0 | 13.0 |
| Velvet | Auto | 415 / 504 | 82.3% | 344.974 | 684.5 | 11.0 | 12,866.0 |
| Velvet | Duper | 292 / 504 | 57.9% | 1,039.652 | 2,062.8 | 0.0 | 15,077.0 |
| Velvet | lean-smt | 302 / 504 | 59.9% | 201.514 | 399.8 | 14.0 | 5,942.0 |
| **Velvet** | **Crush** | **484 / 504** | **96.0%** | **171.406** | **340.1** | **0.0** | **10,386.0** |
| Velvet | `grind` | 444 / 504 | 88.1% | 21.409 | 42.5 | 0.0 | 3,000.0 |
| PLean | Auto | 168 / 192 | 87.5% | 301.027 | 1,567.9 | 0.0 | 17,280.7 |
| PLean | Duper | 71 / 192 | 37.0% | 81.281 | 423.3 | 0.0 | 2,174.6 |
| PLean | lean-smt | 96 / 192 | 50.0% | 272.561 | 1,419.6 | 0.0 | 16,704.4 |
| **PLean** | **Crush** | **174 / 192** | **90.6%** | **1,378.833** | **7,181.4** | **0.0** | **301,768.7** |
| PLean | `grind` | 155 / 192 | 80.7% | 76.005 | 395.9 | 0.0 | 3,859.6 |

`Auto` is the host project's lean-auto backend. In LeanHammer, its lane is the
Auto translation and monomorphization pipeline feeding Duper. `Duper` invokes
Duper directly after host preprocessing. PLean bounds Duper at one second of
saturation and 20,000 heartbeats per VC, but does not cap the generated file,
so all 192 VCs receive an attempt. `grind` is Lean's kernel-checked tactic.
`lean-smt` is [ufmg-smite/lean-smt](https://github.com/ufmg-smite/lean-smt),
which unlike the trusted Crush lane returns a checked Lean proof or nothing.

Every lane in a corpus is measured on the same verification conditions: the
lean-smt lanes were added on 2026-09-04 and their VC identities were diffed
against the recorded Crush lanes and found identical (20, 38, 504, and 192
respectively), so the `Solved / total` and `Coverage` columns are directly
comparable. The timing columns are not measured in the same session — the
lean-smt rows come from the 2026-09-03/04 runs and the other rows from the
recorded runs — so read per-lane times as indicative rather than as a
controlled head-to-head. Coverage was confirmed to reproduce: re-running
Cashmere and LeanHammer reproduced every lane's solved set exactly, with zero
per-VC status disagreements.

Across the 250 VCs where the two lanes were compared directly on LeanHammer,
Cashmere, and PLean, there is no VC that lean-smt closes and Crush does not;
lean-smt's solved set is a strict subset of Crush's.

The published figures omit Loom, whose four VCs are too few for a coverage bar
or curve to carry a percentage, so they report LeanHammer, Cashmere, Velvet,
and PLean. The tables above and the recorded TSVs keep all five corpora; pass
`--exclude-suite loom` to reproduce the figure set.

Every backend has zero missing attempts. `Solved / total` therefore uses the
same denominator and exact VC identities within a corpus. `Total` sums
tactic-local attempt time; `Avg`, `Min`, and `Max` describe individual
attempts. Bold rows compare coverage first and average time when coverage ties.
The runs use one repeat, and some baseline and trusted-Crush lanes were
measured separately. Treat timings as reproducible regression measurements,
not statistically stable performance claims.

`plot-time-coverage.py` plots the same measurements as coverage against time,
one curve per backend and one panel per corpus, so a backend that closes fewer
VCs but closes them sooner is visible rather than averaged away. It needs
matplotlib and no harness invokes it; the
[script guide](scripts/README.md#7-time-versus-coverage-figures-from-recorded-data)
gives a self-contained command sequence that draws both time figures from the
retained inputs in `scripts/benchmark-data`.

## Outcome Breakdown

| Corpus | Backend | Success | Translation error | Timeout | Failed to prove | Total |
|---|---|---:|---:|---:|---:|---:|
| LeanHammer | Auto | 8 | 1 | 0 | 11 | 20 |
| LeanHammer | Duper | 12 | 0 | 1 | 7 | 20 |
| LeanHammer | lean-smt | 12 | 5 | 0 | 3 | 20 |
| LeanHammer | Crush | 19 | 0 | 1 | 0 | 20 |
| LeanHammer | `grind` | 16 | 0 | 0 | 4 | 20 |
| Loom | Auto | 4 | 0 | 0 | 0 | 4 |
| Loom | Duper | 1 | 0 | 0 | 3 | 4 |
| Loom | Crush | 4 | 0 | 0 | 0 | 4 |
| Loom | `grind` | 4 | 0 | 0 | 0 | 4 |
| Cashmere | Auto | 18 | 0 | 0 | 20 | 38 |
| Cashmere | Duper | 21 | 0 | 1 | 16 | 38 |
| Cashmere | lean-smt | 17 | 0 | 0 | 21 | 38 |
| Cashmere | Crush | 38 | 0 | 0 | 0 | 38 |
| Cashmere | `grind` | 19 | 0 | 0 | 19 | 38 |
| Velvet | Auto | 415 | 0 | 0 | 89 | 504 |
| Velvet | Duper | 292 | 0 | 133 | 79 | 504 |
| Velvet | lean-smt | 302 | 82 | 0 | 120 | 504 |
| Velvet | Crush | 484 | 0 | 14 | 6 | 504 |
| Velvet | `grind` | 444 | 0 | 0 | 60 | 504 |
| PLean | Auto | 168 | 6 | 0 | 18 | 192 |
| PLean | Duper | 71 | 0 | 19 | 102 | 192 |
| PLean | lean-smt | 96 | 1 | 0 | 95 | 192 |
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

The checked reconstruction measurement covers the same 754 VC identities as
the headline workload, so its denominators line up with the [Main
Comparison](#main-comparison). It compares trusted verification, Core
reconstruction, strict Alethe replay, and the reconstruction portfolio on the
same recorded Crush inputs. Loom is absent because the run measures only the
corpora the figures report.

| Corpus | Verify solved / total | Checked proof / total | SMT cohort / verify solved | Core / SMT cohort | Alethe / SMT cohort | Portfolio / SMT cohort |
|---|---:|---:|---:|---:|---:|---:|
| LeanHammer | 19 / 20 | 19 / 20 | 15 / 19 | 15 / 15 | 11 / 15 | 15 / 15 |
| Cashmere | 38 / 38 | 38 / 38 | 23 / 38 | 23 / 23 | 0 / 23 | 23 / 23 |
| Velvet | 481 / 504 | 473 / 504 | 296 / 481 | 287 / 296 | 26 / 296 | 287 / 296 |
| PLean | 174 / 192 | 153 / 192 | 172 / 174 | 151 / 172 | 0 / 172 | 151 / 172 |
| **Total** | **712 / 754** | **683 / 754** | **506 / 712** | **476 / 506** | **37 / 506** | **476 / 506** |

These are three different questions, and only the second one counts proofs.

`Verify solved` is the trusted lane: Crush accepted the solver's verdict, and
no proof term was built. `Checked proof` is the portfolio lane's count of VCs
closed with a Lean proof term the kernel accepted, **by whichever route** —
certificate replay, core-directed reconstruction, a selected Lean fact, or
checked pre-SMT reconstruction all count. This is the number to quote for how
many proofs Crush produces: **683 of 754 (90.6%)**.

`reconstruction.svg` plots the `Checked proof` measure for all three lanes
over every VC: Core 684 / 754, Alethe 195 / 754, Portfolio 683 / 754. Core
edges out Portfolio by one VC, since the portfolio tries Alethe replay first
and can fail where core-directed reconstruction alone succeeds.

The last three columns answer the narrower question of certificate replay, and
their denominator is the `SMT cohort`: verify-lane successes whose profile
records that SMT actually returned `unsat`. Pre-SMT closures are excluded from
both numerator and denominator by construction, so `Portfolio / SMT cohort`
(476 / 506) is a replay rate, **not** a proof count — it omits 207 VCs that
Crush closes with a kernel-checked proof without the solver ever returning
`unsat`. Quoting 476 as the number of proofs understates the result.

### Reconstruction Gaps

| Corpus | Lane | Failure mode | SMT-cohort VCs |
|---|---|---|---:|
| LeanHammer | Alethe | certificate error | 2 |
| LeanHammer | Alethe | assumption/rule gap | 1 |
| LeanHammer | Alethe | term decoder gap | 1 |
| Cashmere | Alethe | certificate error | 23 |
| Velvet | Core | reconstruction failed | 6 |
| Velvet | Core | timeout | 3 |
| Velvet | Alethe | certificate error | 239 |
| Velvet | Alethe | assumption/rule gap | 22 |
| Velvet | Alethe | term decoder gap | 9 |
| Velvet | Portfolio | Alethe certificate error + Core failed | 6 |
| Velvet | Portfolio | timeout | 3 |
| PLean | Core | reconstruction failed | 5 |
| PLean | Core | solver `unknown` | 4 |
| PLean | Core | host tactic failed | 12 |
| PLean | Alethe | certificate error | 172 |
| PLean | Portfolio | Alethe certificate error + Core failed | 5 |
| PLean | Portfolio | solver `unknown` | 4 |
| PLean | Portfolio | host tactic failed | 12 |

Certificate errors in this run are cvc5 proof-output failures involving
`DUMMY_SKOLEM`. Rule and term gaps are replay coverage limitations. No VC is
skipped for file termination: every lane reached all 754 VCs.

### Reconstruction Comparison

The table above compares Crush's own lanes on Crush's recorded inputs. A
cross-tool comparison needs a denominator neither tool controls, so
`reconstruction-comparison.tsv` compares `smt-only`, `crush-alethe`, and
`crush-portfolio` over the exact VC-identity intersection of those lanes, the
same matching rule the [Aligned VCs](#aligned-vcs) table uses. Produce it
with:

```sh
bash benchmark-reconstruction.sh --case_study LeanHammer
```

It reports two distinct measures per lane. `Checked proof / matched` counts
matched VCs closed with a Lean proof term the kernel accepted by whichever
route the lane took, so a goal Crush closed by checked pre-SMT reconstruction
counts even though no certificate was replayed. `Certificate replay / SMT
cohort` asks the narrower question over the matched VCs whose trusted Crush
lane recorded an SMT `unsat`, using each lane's own accept set, so its
`Alethe` and `Portfolio` values agree with the table above whenever the
matched set covers the whole cohort.

Three properties of lean-smt shape how its rows read. It closes a goal only
when it also replays cvc5's Alethe certificate, so it is never comparable with
the trusted-Crush headline row. It reports an Alethe rule it cannot replay by
leaving that step as an open goal rather than by failing, so the harness checks
the goal list itself and records those VCs as `rule-gap` instead of counting
them solved. And it drives cvc5 through the in-process `lean-cvc5` bindings
rather than the `cvc5` executable the other lanes use, so its solver build is
the one its Lake package links; `metadata.tsv` records the resolved lean-smt
commit.

The same measurements also drive `reconstruction-over-time.svg`, which plots
reconstructed VCs against tactic-local time over the matched cohort.

Only LeanHammer's pinned revision already requires lean-smt. Cashmere, Velvet,
and PLean get it from a recorded patch under
[`scripts/patches`](scripts/patches), applied to a checkout of the same pinned
revision the run measures: the patch adds `require Smt`, and for PLean also
substitutes the backend inside `PLean/Verify/Tactic.lean` the way the `grind`
lane's patch does. The harness then runs `lake update Smt` and aborts if any
revision the corpus already pinned moved, so every lane measures one Mathlib
closure. All four corpora measure one lean-smt revision, lean-smt's
`no_mathlib` branch: its `main` branch requires Mathlib v4.33.0 while every
corpus here pins v4.32.2. The exact commands are in the
[script guide](scripts/README.md#6-lean-smt-across-every-corpus).

### lean-smt

Measured on 2026-09-03 in one LeanHammer run whose five headline lanes and
four Crush reconstruction lanes share the same 20 VC identities, verified with
`--require-uniform-headline`. It is reported separately from the tables above
because it is a different measurement: lean-crush at `5408ea4` with a dirty
working tree, lean-smt at `e5025665`, LeanHammer at `df4dd136`, cvc5 1.3.4,
`SMT_TIMEOUT=5`, `SMT_MONO=true`. Its Auto, Duper, Crush, and `grind` coverage
reproduces the recorded LeanHammer numbers exactly (8, 12, 19, and 16 of 20).

| Backend | Solved / total | Coverage | Avg (ms) | Min (ms) | Max (ms) |
|---|---:|---:|---:|---:|---:|
| Auto | 8 / 20 | 40.0% | 485.2 | 2.0 | 1,703.0 |
| Duper | 12 / 20 | 60.0% | 1,013.9 | 49.0 | 16,009.0 |
| lean-smt | 12 / 20 | 60.0% | 93.7 | 50.0 | 144.0 |
| **Crush** | **19 / 20** | **95.0%** | **548.6** | **3.0** | **5,384.0** |
| `grind` | 16 / 20 | 80.0% | 4.6 | 0.0 | 13.0 |

The Crush row trusts the SMT verdict, so it is not comparable with lean-smt,
which returns a checked proof or nothing. The reconstruction table below is the
comparable one.

| Lane | Checked proof / matched | Coverage | Common | Avg (ms) | Common avg (ms) | Certificate replay / SMT cohort |
|---|---:|---:|---:|---:|---:|---:|
| lean-smt | 12 / 20 | 60.0% | 10 | 102.1 | 99.0 | 10 / 15 |
| Alethe | 13 / 20 | 65.0% | 10 | 533.2 | 574.7 | 11 / 15 |
| **Portfolio** | **19 / 20** | **95.0%** | **10** | **297.2** | **318.4** | **15 / 15** |

On the 10 VCs all three lanes prove, lean-smt is the fastest by roughly 3x
over Crush's portfolio and 5.8x over strict Alethe. Crush's portfolio proves
19 of 20, and every VC whose trusted lane saw an SMT `unsat` (15 of 15).
Strict Alethe and lean-smt reconstruct 11 and 10 of that cohort.

| Lane | Failure mode | VCs |
|---|---|---:|
| lean-smt | encoding rejected | 5 |
| lean-smt | solver `sat` | 3 |
| Alethe | certificate error | 2 |
| Alethe | solver `unknown` | 2 |
| Alethe | assumption/rule gap | 1 |
| Alethe | term decoder gap | 1 |
| Alethe | solver `sat` | 1 |
| Portfolio | solver `unknown` | 1 |

lean-smt's failures are dominated by encoding rather than replay: on the five
`translation-failed` VCs it never obtained a proof to replay. Two were a
higher-order arrow reaching cvc5's parser as `Symbol '->' not declared as a
type`, one a variable-width `BitVec`, one an empty datatype declaration, and
one a `cannot translate` from its own translators. It left no Alethe step
unreplayed on this workload, so it records no `rule-gap`. It also emits no
certificate size or phase metrics, so it contributes no rows to the Alethe
scaling or phase tables.

### Phase Timing

| Corpus | Lane | Accounted (s) | Largest profiler phases |
|---|---|---:|---|
| LeanHammer | Verify | 11.520 | solve 97.7%, translate 1.2% |
| LeanHammer | Core | 9.816 | solve 96.6%, reconstruct 1.7% |
| LeanHammer | Alethe | 14.887 | solve 85.3%, replay 13.5% |
| LeanHammer | Portfolio | 11.414 | solve 83.7%, replay 14.0% |
| Cashmere | Verify | 18.645 | solve 66.8%, instantiate 29.7%, translate 2.4% |
| Cashmere | Core | 15.928 | solve 64.7%, instantiate 28.0%, reconstruct 3.6% |
| Cashmere | Alethe | 23.473 | solve 67.8%, instantiate 29.6%, translate 2.3% |
| Cashmere | Portfolio | 16.501 | solve 64.3%, instantiate 28.5%, reconstruct 3.5% |
| Velvet | Verify | 344.132 | solve 83.3%, fallback solve 6.5%, instantiate 5.4% |
| Velvet | Core | 398.484 | solve 64.0%, reconstruct 23.5%, fallback solve 5.6% |
| Velvet | Alethe | 373.200 | solve 81.4%, fallback solve 6.0%, instantiate 5.3% |
| Velvet | Portfolio | 419.274 | solve 61.2%, reconstruct 23.2%, fallback solve 5.4% |
| PLean | Verify | 1,670.468 | solve 97.4%, translate 1.8% |
| PLean | Core | 1,842.069 | solve 71.2%, pre-reconstruct 20.1%, reconstruct 7.6% |
| PLean | Alethe | 1,150.854 | solve 94.7%, translate 4.2% |
| PLean | Portfolio | 1,830.347 | solve 71.9%, pre-reconstruct 19.7%, reconstruct 7.3% |

`Accounted` sums profiler events rather than process wall time. One host VC may
invoke Crush more than once. `phase-summary.tsv` records event count, total,
mean, minimum, maximum, and percentage for every phase.

### Alethe Scaling

| Corpus | Replayed VCs | Commands | Replay time (ms) | Pearson r | R-squared | ms / 100 commands |
|---|---:|---:|---:|---:|---:|---:|
| LeanHammer | 13 | 3-231 | 5.0-948.7 | 0.9170 | 0.8408 | 327.4 |
| Velvet | 27 | 10-275 | 25.8-1,393.6 | 0.6686 | 0.4470 | 343.8 |

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
