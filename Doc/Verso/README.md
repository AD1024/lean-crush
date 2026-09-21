# lean-crush Verso manual

This is an optional documentation package. Its Verso dependencies are isolated
from the root `lean-crush` package.

The `Documentation` GitHub Actions workflow publishes the manual at
<https://ad1024.github.io/lean-crush/>.

From this directory:

```sh
lake build
lake exe crush-docs
python3 -m http.server 8000 --directory _out/html-multi
```

Then open <http://localhost:8000>. The build uses the pinned Lean and Verso
dependencies. Run `lake update` only when intentionally updating those dependencies.

The Lean examples are checked during the build and require both Z3 and cvc5 on
`PATH`; CI uses Z3 5.1.0 and cvc5 1.3.4. Edit the sources under `CrushManual/`,
then run both build and render before publishing. The HTML under `_out/` is
generated output.

Image URLs are relative to the manual's HTML base URL: use `figures/name.svg`,
without `../` prefixes. Check previews under a path such as `/lean-crush/`
as well as `/`, since root-only previews can hide broken deployment paths.

The benchmark images in `figures/` use the raw measurements under
`BenchmarkResults/paper/`. Recompute the summaries before drawing all six SVGs,
so stale derived reports cannot change the counts. The time-coverage renderer
requires Matplotlib (`python3 -m pip install matplotlib` in a virtual environment).
From the repository root:

```sh
manual_data=BenchmarkResults/paper
for suite in curated corpora plean; do
  python3 scripts/benchmark-report.py \
    --measurements "$manual_data/$suite/measurements.tsv" \
    --profiles "$manual_data/$suite/profile-events.tsv" \
    --out-dir "$manual_data/$suite"
done
python3 scripts/plot-benchmarks.py \
  "$manual_data/curated" "$manual_data/corpora" "$manual_data/plean" \
  --out-dir Doc/Verso/figures --exclude-suite loom \
  --only outcomes \
  --only reconstruction-failures --only phase-breakdown \
  --only alethe-replay-scaling
manual_curves=$(mktemp -d)
python3 scripts/plot-time-coverage.py \
  "$manual_data/curated" "$manual_data/corpora" "$manual_data/plean" \
  --out-dir "$manual_curves" --exclude-suite loom \
  --only main --only reconstruction --format svg --layout grid
cp "$manual_curves/coverage-over-time.svg" \
  "$manual_curves/reconstruction-over-time.svg" Doc/Verso/figures/
```

Without a local run, set `manual_data=$(mktemp -d)` and unpack
`scripts/benchmark-data/eval-data.zip` there before the same commands.
The archive preserves the raw data used by this revision of the manual.

Use final `measurements.tsv` verdicts for VC coverage. `profile-events.tsv`
also contains failed attempts later recovered by host proof search; those
events must not veto a completed checked proof. Keep whole-workload coverage
separate from the narrower SMT-cohort attribution in the chapter.
