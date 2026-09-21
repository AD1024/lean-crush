# Benchmarks

The headline comparison evaluates Auto, Duper,
[lean-smt](https://github.com/ufmg-smite/lean-smt), trusted Crush,
kernel-checked Crush, and `grind` on one fixed set of verification-condition
identities per corpus. The detailed [reconstruction study](#reconstruction)
separates whole-VC successes from reconstruction within the SMT-`unsat` cohort.

Machine-readable inputs are retained under
[`scripts/benchmark-data`](scripts/benchmark-data),
and [`scripts/README.md`](scripts/README.md) gives
self-contained reproduction commands.
The values below are the latest normalized comparison in
`main/` inside `scripts/benchmark-data/eval-data.zip`;
run `scripts/render-paper-artifacts.sh` to regenerate tables and figures under
`BenchmarkResults/figures`. The
[Verso benchmark chapter](https://ad1024.github.io/lean-crush/Benchmarks/)
embeds separate snapshots from `Doc/Verso/figures`; those assets have not yet
been refreshed to this measurement.

## Main Comparison

| Corpus | Backend | Solved / total | Coverage | Total (s) | Avg (ms) | Min (ms) | Max (ms) |
|---|---|---:|---:|---:|---:|---:|---:|
| Curated | Auto | 17 / 20 | 85.0% | 5.401 | 270.1 | 30.0 | 336.0 |
| Curated | Duper | 12 / 20 | 60.0% | 20.939 | 1,047.0 | 54.0 | 16,635.0 |
| Curated | lean-smt | 12 / 20 | 60.0% | 1.814 | 90.7 | 48.0 | 152.0 |
| Curated | Crush (SMT trusted) | 19 / 20 | 95.0% | 9.209 | 460.5 | 4.0 | 5,284.0 |
| Curated | Crush (kernel-checked) | 19 / 20 | 95.0% | 11.629 | 581.5 | 4.0 | 5,273.0 |
| Curated | `grind` | 16 / 20 | 80.0% | 0.093 | 4.7 | 0.0 | 15.0 |
| Loom | Auto | 4 / 4 | 100.0% | 0.974 | 243.5 | 44.0 | 607.0 |
| Loom | Duper | 1 / 4 | 25.0% | 0.454 | 113.5 | 36.0 | 174.0 |
| Loom | Crush (SMT trusted) | 4 / 4 | 100.0% | 0.418 | 104.5 | 53.0 | 139.0 |
| Loom | `grind` | 4 / 4 | 100.0% | 0.048 | 12.0 | 7.0 | 17.0 |
| Cashmere | Auto | 18 / 38 | 47.4% | 5.379 | 141.6 | 2.0 | 631.0 |
| Cashmere | Duper | 21 / 38 | 55.3% | 65.087 | 1,712.8 | 1.0 | 40,739.0 |
| Cashmere | lean-smt | 17 / 38 | 44.7% | 5.547 | 146.0 | 41.0 | 244.0 |
| Cashmere | Crush (SMT trusted) | 38 / 38 | 100.0% | 18.920 | 497.9 | 1.0 | 1,207.0 |
| Cashmere | Crush (kernel-checked) | 38 / 38 | 100.0% | 19.770 | 520.3 | 2.0 | 1,301.0 |
| Cashmere | `grind` | 19 / 38 | 50.0% | 0.289 | 7.6 | 4.0 | 13.0 |
| Velvet | Auto | 415 / 504 | 82.3% | 344.974 | 684.5 | 11.0 | 12,866.0 |
| Velvet | Duper | 292 / 504 | 57.9% | 1,039.652 | 2,062.8 | 0.0 | 15,077.0 |
| Velvet | lean-smt | 302 / 504 | 59.9% | 201.514 | 399.8 | 14.0 | 5,942.0 |
| Velvet | Crush (SMT trusted) | 478 / 504 | 94.8% | 356.946 | 708.2 | 0.0 | 11,485.0 |
| Velvet | Crush (kernel-checked) | 472 / 504 | 93.7% | 578.785 | 1,148.4 | 0.0 | 73,377.0 |
| Velvet | `grind` | 444 / 504 | 88.1% | 21.409 | 42.5 | 0.0 | 3,000.0 |
| PLean | Auto | 168 / 192 | 87.5% | 301.027 | 1,567.9 | 0.0 | 17,280.7 |
| PLean | Duper | 71 / 192 | 37.0% | 81.281 | 423.3 | 0.0 | 2,174.6 |
| PLean | lean-smt | 96 / 192 | 50.0% | 272.561 | 1,419.6 | 0.0 | 16,704.4 |
| PLean | Crush (SMT trusted) | 174 / 192 | 90.6% | 357.689 | 1,863.0 | 0.0 | 26,883.9 |
| PLean | Crush (kernel-checked) | 163 / 192 | 84.9% | 472.147 | 2,459.1 | 0.0 | 26,783.3 |
| PLean | `grind` | 155 / 192 | 80.7% | 76.005 | 395.9 | 0.0 | 3,859.6 |

Crush appears twice. `Crush (SMT trusted)` is the `crush-verify` lane, which
may accept SMT `unsat` without a checked proof. `Crush (kernel-checked)` is the
`crush-portfolio` lane, which requires a kernel-checked Lean proof. Both lanes
can close goals from selected facts or checked pre-SMT reasoning without
calling the solver. The optional backward rule search is controlled by
`crush.preReconstruct.ruleSearch`, defaults to `false`, and has the same
setting in both lanes. Strict Alethe replay skips these early closures inside
Crush so that successful tactic calls exercise certificate replay.

On the four paper corpora (754 VCs, excluding Loom), the headline totals are
Auto **609 (80.8%)**, Duper **396 (52.5%)**, lean-smt **427 (56.6%)**,
`grind` **634 (84.1%)**, trusted Crush **709 (94.0%)**, and kernel-checked
Crush **692 (91.8%)**. The last number counts successful whole-VC attempts;
the [reconstruction report](#reconstruction) currently applies an additional
profiler-outcome filter and reports 688. The four-VC discrepancy is explained
there.

`Auto` is the host project's lean-auto backend. On the curated suite it is
lean-auto invoked directly: its translation and monomorphization pipeline, with
Duper bound as the prover for the residual first-order goal.
`Duper` invokes Duper directly after host preprocessing. PLean bounds Duper at
one second of saturation and 20,000 heartbeats per VC, but does not cap the
generated file,
so all 192 VCs receive an attempt. `grind` is Lean's kernel-checked tactic.
`lean-smt` is [ufmg-smite/lean-smt](https://github.com/ufmg-smite/lean-smt),
which unlike the trusted Crush lane returns a checked Lean proof or nothing.

Every lane in a corpus is measured on the same verification conditions: the
lean-smt lanes were added on 2026-09-04 and their VC identities were diffed
against the recorded Crush lanes and found identical (20, 38, 504, and 192
respectively), so the `Solved / total` and `Coverage` columns are directly
comparable. Both Crush lanes on the four paper corpora come from the
2026-09-18 study on one host. The baseline lanes retain earlier measurements,
including the 2026-09-03/04 lean-smt runs; Loom also retains its older Crush
measurement. Cross-backend timings therefore span sessions, while the paired
trusted and checked Crush measurements share a host and run configuration.

The preceding 2026-09-17 run reported 708 trusted and 687 portfolio successes;
the new run reports 709 and 692. The portfolio change is +6 on PLean and -1
on Velvet. The older 715 trusted total used a separate Velvet measurement of
484 successes; it is not the before-change result from this paired study.
Commit `c4cb643` leaves the default trusted pre-SMT behavior unchanged.
Differences between single runs near the solver time cap should not be
attributed to that change alone.

Across the 250 VCs where the two lanes were compared directly on Curated,
Cashmere, and PLean, there is no VC that lean-smt closes and Crush does not;
lean-smt's solved set is a strict subset of Crush's.

The published figures omit Loom, whose four VCs are too few for a coverage bar
or curve to carry a percentage, so they report Curated, Cashmere, Velvet,
and PLean. The tables above and the recorded TSVs keep all five corpora; pass
`--exclude-suite loom` to reproduce the figure set.

Every backend has zero missing attempts. `Solved / total` therefore uses the
same denominator and exact VC identities within a corpus. `Total` sums
tactic-local attempt time; `Avg`, `Min`, and `Max` describe individual
attempts. The runs use one repeat. Treat timings as individual regression
measurements, not statistically stable performance claims.

`plot-time-coverage.py` plots the same measurements as coverage against time,
one curve per backend and one panel per corpus, so a backend that closes fewer
VCs but closes them sooner is visible rather than averaged away. It needs
matplotlib; the
[script guide](scripts/README.md#2-draw-the-figures)
gives a self-contained command sequence that draws both time figures from the
retained inputs in `scripts/benchmark-data`.

## Outcome Breakdown

| Corpus | Backend | Success | Translation error | Timeout | Failed to prove | Total |
|---|---|---:|---:|---:|---:|---:|
| Curated | Auto | 17 | 3 | 0 | 0 | 20 |
| Curated | Duper | 12 | 0 | 1 | 7 | 20 |
| Curated | lean-smt | 12 | 5 | 0 | 3 | 20 |
| Curated | Crush (SMT trusted) | 19 | 0 | 1 | 0 | 20 |
| Curated | Crush (kernel-checked) | 19 | 0 | 1 | 0 | 20 |
| Curated | `grind` | 16 | 0 | 0 | 4 | 20 |
| Loom | Auto | 4 | 0 | 0 | 0 | 4 |
| Loom | Duper | 1 | 0 | 0 | 3 | 4 |
| Loom | Crush (SMT trusted) | 4 | 0 | 0 | 0 | 4 |
| Loom | `grind` | 4 | 0 | 0 | 0 | 4 |
| Cashmere | Auto | 18 | 0 | 0 | 20 | 38 |
| Cashmere | Duper | 21 | 0 | 1 | 16 | 38 |
| Cashmere | lean-smt | 17 | 0 | 0 | 21 | 38 |
| Cashmere | Crush (SMT trusted) | 38 | 0 | 0 | 0 | 38 |
| Cashmere | Crush (kernel-checked) | 38 | 0 | 0 | 0 | 38 |
| Cashmere | `grind` | 19 | 0 | 0 | 19 | 38 |
| Velvet | Auto | 415 | 0 | 0 | 89 | 504 |
| Velvet | Duper | 292 | 0 | 133 | 79 | 504 |
| Velvet | lean-smt | 302 | 82 | 0 | 120 | 504 |
| Velvet | Crush (SMT trusted) | 478 | 0 | 20 | 6 | 504 |
| Velvet | Crush (kernel-checked) | 472 | 0 | 20 | 12 | 504 |
| Velvet | `grind` | 444 | 0 | 0 | 60 | 504 |
| PLean | Auto | 168 | 6 | 0 | 18 | 192 |
| PLean | Duper | 71 | 0 | 19 | 102 | 192 |
| PLean | lean-smt | 96 | 1 | 0 | 95 | 192 |
| PLean | Crush (SMT trusted) | 174 | 0 | 16 | 2 | 192 |
| PLean | Crush (kernel-checked) | 163 | 0 | 17 | 12 | 192 |
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
| Curated | Auto | 20 | 0 | 2 | 17 | 1 | 305.6 | 212.1 |
| Curated | Duper | 20 | 1 | 8 | 11 | 0 | 95.4 | 208.4 |
| Curated | lean-smt | 20 | 0 | 7 | 12 | 1 | 101.1 | 212.2 |
| Curated | `grind` | 20 | 0 | 3 | 16 | 1 | 5.6 | 210.8 |
| Loom | Auto | 4 | 0 | 0 | 4 | 0 | 243.5 | 104.5 |
| Loom | Duper | 4 | 0 | 3 | 1 | 0 | 36.0 | 53.0 |
| Loom | `grind` | 4 | 0 | 0 | 4 | 0 | 12.0 | 104.5 |
| Cashmere | Auto | 38 | 0 | 20 | 18 | 0 | 101.1 | 222.1 |
| Cashmere | Duper | 38 | 0 | 17 | 21 | 0 | 98.5 | 238.7 |
| Cashmere | lean-smt | 38 | 0 | 21 | 17 | 0 | 137.1 | 148.4 |
| Cashmere | `grind` | 38 | 0 | 19 | 19 | 0 | 7.2 | 210.5 |
| Velvet | Auto | 504 | 10 | 73 | 405 | 16 | 178.8 | 418.7 |
| Velvet | Duper | 504 | 3 | 189 | 289 | 23 | 198.7 | 246.6 |
| Velvet | lean-smt | 504 | 9 | 185 | 293 | 17 | 145.7 | 400.6 |
| Velvet | `grind` | 504 | 9 | 43 | 435 | 17 | 18.9 | 370.4 |
| PLean | Auto | 192 | 0 | 6 | 168 | 18 | 885.8 | 1,183.0 |
| PLean | Duper | 192 | 0 | 103 | 71 | 18 | 428.2 | 530.8 |
| PLean | lean-smt | 192 | 0 | 78 | 96 | 18 | 733.5 | 578.4 |
| PLean | `grind` | 192 | 0 | 19 | 155 | 18 | 208.3 | 1,130.9 |

Each row compares trusted Crush with one baseline. `Matched` is the exact
VC-identity intersection. `Baseline only`, `Crush only`, `Both`, and `Neither`
partition that intersection. Timing averages include only `Both` VCs, so a
backend cannot appear faster by failing more goals. These rows do not compare
two baselines with each other.

## Reconstruction

The reconstruction measurement in `crush-modes/` inside `scripts/benchmark-data/eval-data.zip`
covers the same 754 VC identities as the [Main Comparison](#main-comparison).
It measures trusted verification, strict Alethe replay, and the reconstruction
portfolio. **Core was not measured** in this run; a dash means unavailable,
not zero. Loom is absent.

| Corpus | Verify solved / total | Portfolio checked (reported) / total | SMT cohort / verify solved | Core / SMT cohort | Alethe / SMT cohort | Portfolio / SMT cohort |
|---|---:|---:|---:|---:|---:|---:|
| Curated | 19 / 20 | 19 / 20 | 15 / 19 | — | 12 / 15 | 15 / 15 |
| Cashmere | 38 / 38 | 38 / 38 | 23 / 38 | — | 0 / 23 | 23 / 23 |
| Velvet | 478 / 504 | 472 / 504 | 293 / 478 | — | 26 / 293 | 287 / 293 |
| PLean | 174 / 192 | 159 / 192 | 172 / 174 | — | 0 / 172 | 157 / 172 |
| **Total** | **709 / 754** | **688 / 754** | **503 / 709** | — | **38 / 503** | **482 / 503** |

`Verify solved` counts all trusted-lane successes, including selected facts
and early checked closures. `SMT cohort` includes only those successes with a
verify-lane profiler event recording SMT `unsat`. Its 503 VCs form the
denominator of the last three columns. Portfolio success within this cohort
may use either certificate replay or core-directed reconstruction; it is not
a certificate-replay count alone.

`Portfolio checked (reported)` reproduces `portfolio_checked` from
`reconstruction-summary.tsv`: **688 / 754 (91.2%)**. The current reporter
requires a passing VC and, when profiler events exist, accepts it only if
every event has a checked-success outcome. Four passing PLean VCs contain
both successful reconstruction events and `unknown` events, so this filter
counts 159 while headline coverage counts 163. Consequently, the reports
disagree by four even though they use the same measurements. This is a
reporting discrepancy, not evidence of four invalid proofs; it must be
resolved before the two measures can be used interchangeably.

For comparison, the preceding run reported 687 portfolio successes and 683
profiler-filtered checked VCs. The changes are therefore **687 → 692** for
headline coverage and **683 → 688** for the reconstruction report, each +5.

The current `reconstruction.svg` renderer uses reported checked coverage over
all VCs: **Alethe 195 / 754**, **Portfolio 688 / 754**, and no Core result.
The portfolio's **482 / 503** cohort count answers a narrower question and
must not replace whole-VC coverage. A VC outside the trusted lane's SMT cohort
need not have followed the same route in the checked lane.

### Reconstruction Gaps

| Corpus | Lane | Reported failure mode | SMT-cohort VCs |
|---|---|---|---:|
| Curated | Alethe | `certificate-error` | 2 |
| Curated | Alethe | `term-gap` | 1 |
| Cashmere | Alethe | `certificate-error` | 23 |
| Velvet | Alethe | `certificate-error` | 236 |
| Velvet | Portfolio | `certificate-error+core-failed` | 4 |
| Velvet | Portfolio | `timeout` | 2 |
| PLean | Alethe | `certificate-error` | 172 |
| PLean | Portfolio | `certificate-error+core-failed` | 8 |
| PLean | Portfolio | `solver-unknown` | 4 |
| PLean | Portfolio | `tactic` | 3 |

These counts reproduce `reconstruction-failures.tsv` and use the same
profiler filter as the table above. In particular, PLean's four portfolio
`solver-unknown` records include the four passing VCs discussed above; they
should not be read as four failed whole-VC attempts. Every measured lane
attempted all 754 VCs.

Almost every remaining failure is a `certificate-error`: cvc5's `DUMMY_SKOLEM`
proof-output limitation, which no amount of replay coverage can reach because
no usable certificate is emitted. Replay coverage itself now accounts for a
single VC in the whole dataset -- one `term-gap` on Curated. Velvet's earlier
22 `rule-gap` and 9 `term-gap` records are gone: the replay fixes closed them,
and this run measures the Alethe lane once rather than in two studies whose
copies had drifted apart.

### Reconstruction Comparison

The table above compares Crush's own lanes on Crush's recorded inputs. A
cross-tool comparison needs a denominator neither tool controls, so
`reconstruction-comparison.tsv` compares `smt-only`, `crush-alethe`, and
`crush-portfolio` over the exact VC-identity intersection of those lanes, the
same matching rule the [Aligned VCs](#aligned-vcs) table uses. Produce it
with:

```sh
bash run-experiments.sh --suites curated
```

It reports two distinct measures per lane. `Checked proof / matched` counts
matched VCs closed with a Lean proof term the kernel accepted by whichever
route the lane took, so a goal Crush closed by checked pre-SMT reconstruction
counts even though no certificate was replayed. `Reconstruction / SMT
cohort` asks the narrower question over the matched VCs whose trusted Crush
lane recorded an SMT `unsat`, using each lane's own accept set, so its
`Alethe` and `Portfolio` values agree with the table above when the reports
use the same run and the matched set covers the whole cohort. The same
profiler filtering caveat applies to `Checked proof / matched`.

The renderer's default cross-tool inputs, `reconstruction/` inside `scripts/benchmark-data/eval-data.zip`,
retain the earlier Cashmere and Velvet comparison. That archive has not been
refreshed to the 2026-09-18 Crush study. Cross-tool figures and tables drawn
from it must remain labeled as that separate snapshot; refreshing
`crush-modes` does not update the archive.

Three properties of lean-smt shape how its rows read. It closes a goal only
when it also replays cvc5's Alethe certificate, so its proof guarantee matches
the checked Crush lanes. Headline coverage can still compare all lanes with
their trust policies stated. It reports an Alethe rule it cannot replay by
leaving that step as an open goal rather than by failing, so the harness checks
the goal list itself and records those VCs as `rule-gap` instead of counting
them solved. And it drives cvc5 through the in-process `lean-cvc5` bindings
rather than the `cvc5` executable the other lanes use, so its solver build is
the one its Lake package links; `metadata.tsv` records the resolved lean-smt
commit.

The same measurements also drive `reconstruction-over-time.svg`, which plots
reconstructed VCs against tactic-local time over the matched cohort.

Only the Curated suite's pinned revision already requires lean-smt. Cashmere, Velvet,
and PLean get it from a recorded patch under
[`scripts/patches`](scripts/patches), applied to a checkout of the same pinned
revision the run measures: the patch adds `require Smt`, and for PLean also
substitutes the backend inside `PLean/Verify/Tactic.lean` the way the `grind`
lane's patch does. The harness then runs `lake update Smt` and aborts if any
revision the corpus already pinned moved, so every lane measures one Mathlib
closure. All four corpora measure one lean-smt revision, lean-smt's
`no_mathlib` branch: its `main` branch requires Mathlib v4.33.0 while every
corpus here pins v4.32.2. The exact commands are in the
[script guide](scripts/README.md#3-the-other-studies).

### lean-smt

Measured on 2026-09-03 in one Curated run whose five headline lanes and
four Crush reconstruction lanes share the same 20 VC identities, verified with
`--require-uniform-headline`. It is reported separately from the tables above
because it is a different measurement: lean-crush at `5408ea4` with a dirty
working tree, lean-smt at `e5025665`, the suite at `df4dd136`, cvc5 1.3.4,
`SMT_TIMEOUT=5`, `SMT_MONO=true`. Its Auto, Duper, Crush, and `grind` coverage
reproduces the recorded Curated numbers exactly (8, 12, 19, and 16 of 20).

| Backend | Solved / total | Coverage | Avg (ms) | Min (ms) | Max (ms) |
|---|---:|---:|---:|---:|---:|
| Auto | 8 / 20 | 40.0% | 485.2 | 2.0 | 1,703.0 |
| Duper | 12 / 20 | 60.0% | 1,013.9 | 49.0 | 16,009.0 |
| lean-smt | 12 / 20 | 60.0% | 93.7 | 50.0 | 144.0 |
| **Crush** | **19 / 20** | **95.0%** | **548.6** | **3.0** | **5,384.0** |
| `grind` | 16 / 20 | 80.0% | 4.6 | 0.0 | 13.0 |

This historical Crush row permits trusting the SMT verdict. For a comparison
requiring checked proofs from every lane, use the reconstruction table below.

| Lane | Checked proof / matched | Coverage | Common | Avg (ms) | Common avg (ms) | Reconstruction / SMT cohort |
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
| Curated | Verify | 9.390 | solve 97.5%, translate 1.2%, pre-reconstruct 0.7% |
| Curated | Alethe | 12.493 | solve 80.5%, replay 17.8%, translate 1.1% |
| Curated | Portfolio | 11.367 | solve 79.5%, replay 17.6%, translate 1.0% |
| Cashmere | Verify | 18.686 | solve 67.5%, instantiate 29.0%, translate 2.3% |
| Cashmere | Alethe | 23.356 | solve 69.9%, instantiate 27.6%, translate 2.2% |
| Cashmere | Portfolio | 19.540 | solve 65.1%, instantiate 28.6%, reconstruct 3.0% |
| Velvet | Verify | 350.451 | solve 84.2%, solve-fallback 6.5%, instantiate 4.9% |
| Velvet | Alethe | 387.058 | solve 82.7%, solve-fallback 5.9%, instantiate 4.7% |
| Velvet | Portfolio | 446.514 | solve 63.8%, reconstruct 21.0%, solve-fallback 5.1% |
| PLean | Verify | 1,686.745 | solve 97.4%, translate 1.8%, normalize 0.4% |
| PLean | Alethe | 1,159.880 | solve 94.9%, translate 4.1%, normalize 0.9% |
| PLean | Portfolio | 2,064.561 | solve 82.7%, reconstruct 14.9%, translate 1.7% |

`Accounted` sums profiler events rather than process wall time. One host VC may
invoke Crush more than once. `phase-summary.tsv` records event count, total,
mean, minimum, maximum, and percentage for every phase.

### Alethe Scaling

| Corpus | Replayed VCs | Commands | Replay time (ms) | Pearson r | R-squared | ms / 100 commands |
|---|---:|---:|---:|---:|---:|---:|
| Curated | 14 | 3-231 | 5.8-935.2 | 0.9253 | 0.8562 | 330.4 |
| Velvet | 27 | 10-275 | 23.6-1,335.2 | 0.7110 | 0.5055 | 351.5 |

Each point is one successful strict Alethe replay, averaged by VC across
repeats. Script length is the parsed Alethe command count. Replay time includes
certificate parsing, step replay, proof assembly, and final kernel checking,
but excludes solver time. Cashmere and PLean have no successful certificate
replay samples; their strict-lane successes closed before replay.

## Configuration

The main corpus and Curated lanes use a five-second solver or saturation
limit and one million Lean heartbeats per VC. The exact invocations that
produced the Curated rows -- one per study, with every environment variable
they were run with -- are in the
[script guide](scripts/README.md#3a-reproducing-the-recorded-curated-measurements).
PLean uses the same Crush timeout and heartbeat budget, disables Crush
ground-instantiation fuel, and uses the bounded Duper settings described above.
Builds and imports are excluded from tactic-local timing. The measurements were collected on Apple Silicon arm64
running macOS 26.6 with Z3 4.15.4 and cvc5 1.3.4.

| Component | Auto revision | Duper revision | Crush / `grind` revision |
|---|---|---|---|
| Curated[^lift] | `e4f8b0c` (`auto`) | `57b04df` (`duper`) | `8422791` (`crush`), `cda392a` (`main`) |
| Loom and Cashmere | `78928abc9054b31d0bea85985496490baae95244` | `616f9cd8db660dcd74a1c92b0d19bb50420e1c59` | `ec16b95ff8bbd047248de031cabd3160847e4b1b` |
| Velvet | `d254391d5e84546f96576e5b67dfb6bafe9fc301` | `5a1180338958908323a921255a8d158cf1f26c95` | `e90d79341bb8ef510ec868623e74cfe98feaa4e8` |
| PLean | `be39726723e71f9aa1e02c6cfeeae9b0c31b8947` | `3557f1f0fa5246ee88fcde3776f3973349049968` | `9c098b4c5ad32faf2a022929b6726d2a182a9e1d` |

Duper is pinned at
`ca7c5862bee2e62e019e6a1b70ce95612b6b6365`. The PLean `grind` lane applies
the recorded pure-`grind` patch and guards against invoking an external
solver. Exact options, toolchains, dirty-state hashes, and per-file wall times
are in the recorded metadata and run files.

The refreshed Crush measurements record lean-crush commit
`c183f06eb81f82823d50b9695a492e48d29eca95` with a dirty working tree. Their
provenance is retained in `crush-modes/*/metadata.tsv` inside `scripts/benchmark-data/eval-data.zip`.
The fold into `main` replaces measurement and profiler rows but does not
replace metadata, so older `main` metadata must not be used to identify the
refreshed Crush build. Baselines, Loom, and the archived cross-tool comparison
retain their original revisions; see the
[dataset README](scripts/benchmark-data/README.md) for the source mapping.

[^lift]: The curated suite keeps one backend per branch of
    [Lean-SMT-Benchmarks](https://github.com/AD1024/Lean-SMT-Benchmarks), so a
    revision names a branch tip rather than one commit the whole suite shares.
    The `lean-smt` lane is measured on the `lean-smt` branch at `ecd10eb`.
    Nothing in the suite depends on LeanHammer: the cases previously lived in a
    fork of it, which made them read as LeanHammer's own benchmark, and the
    `Auto` row is now lean-auto invoked directly rather than through the
    `hammer` tactic.
