#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OUT_DIR="${1:-BenchmarkResults/figures}"

cd "$CRUSH_ROOT"

# Every recorded measurement ships as one archive rather than several hundred
# loose TSVs, so refreshing the data is a single binary change instead of a
# repo-wide add/delete churn. It holds main/, crush-modes/ and reconstruction/.
# Unpack it unless the caller pointed PAPER_DATA_ROOT at loose data of their own.
DATA_ARCHIVE="${PAPER_DATA_ARCHIVE:-scripts/benchmark-data/eval-data.zip}"
DATA_ROOT="${PAPER_DATA_ROOT:-}"
if [[ -z "$DATA_ROOT" && -f "$DATA_ARCHIVE" ]]; then
  if command -v unzip >/dev/null 2>&1; then
    DATA_UNPACKED="$(mktemp -d)"
    trap 'rm -rf "$DATA_UNPACKED"' EXIT
    if unzip -q "$DATA_ARCHIVE" -d "$DATA_UNPACKED"; then
      DATA_ROOT="$DATA_UNPACKED"
    else
      printf 'error: could not unpack %s\n' "$DATA_ARCHIVE" >&2
      exit 1
    fi
  else
    printf 'error: unzip not found; it is needed to read %s\n' "$DATA_ARCHIVE" >&2
    printf 'or set PAPER_DATA_ROOT to an unpacked copy\n' >&2
    exit 1
  fi
fi
DATA_ROOT="${DATA_ROOT:-scripts/benchmark-data}"

# One root, and every figure is drawn from it. There used to be three -- one
# per study -- and because a (suite, lane) could sit in more than one of them,
# the copies drifted: Velvet's Alethe rows were post-fix in one and pre-fix in
# another, so the figure said 239 checked VCs while the prose said 196. With a
# single root each (suite, lane) exists once and cannot disagree with itself.
#
# `run-experiments.sh` writes `corpora/`, `curated/` and `plean/` under one
# directory, which is exactly the shape this wants, so a fresh run is drawn by
# pointing MEASUREMENTS_ROOT at it.
MEASUREMENTS_ROOT="${MEASUREMENTS_ROOT:-$DATA_ROOT}"

# Which suite directories a run root holds depends on how it was measured: a
# full `--case_study all` writes corpora/, curated/ and plean/, while a single
# case study writes only its own (velvet/, cashmere/, ...). Discover them instead
# of assuming the three, so a partial run still draws. A directory counts when it
# carries measurements, which skips figures/ and any stray output.
collect_run_dirs() {
  local root="$1"
  local dir
  COLLECTED=()
  for dir in "$root"/*/; do
    [[ -f "$dir/measurements.tsv" ]] || continue
    COLLECTED+=("${dir%/}")
  done
}

collect_run_dirs "$MEASUREMENTS_ROOT"
RUN_DIRS=(${COLLECTED[@]+"${COLLECTED[@]}"})
if [[ ${#RUN_DIRS[@]} -eq 0 ]]; then
  printf 'error: no measured suite directories under %s\n' "$MEASUREMENTS_ROOT" >&2
  printf 'each needs a measurements.tsv; point MEASUREMENTS_ROOT at your own run,\n' >&2
  printf 'e.g.\n' >&2
  printf '  MEASUREMENTS_ROOT=BenchmarkResults/coverage-<stamp> \\\n' >&2
  printf '  scripts/render-paper-artifacts.sh out/\n' >&2
  exit 1
fi

# A figure is drawn when the lanes it needs were measured. A coverage-only run
# has no `crush-alethe` rows, so its reconstruction figures are skipped rather
# than drawn empty -- the same way the time figures are skipped without
# matplotlib.
lanes_present() {
  local lane
  for lane in "$@"; do
    if awk -F '\t' -v want="$lane" \
        'NR == 1 { for (i = 1; i <= NF; i++) if ($i == "lane") c = i; next }
         c && $c == want { found = 1 }
         END { exit !found }' \
        "${RUN_DIRS[@]/%//measurements.tsv}" 2>/dev/null; then
      return 0
    fi
  done
  return 1
}

HAVE_MODES=true
if ! lanes_present crush-alethe crush-core; then
  HAVE_MODES=false
  printf 'note: no Crush reconstruction lanes under %s; skipping those figures\n' \
    "$MEASUREMENTS_ROOT" >&2
fi

HAVE_RECON=true
if ! lanes_present smt-only; then
  HAVE_RECON=false
  printf 'note: no lean-smt lane under %s; skipping the reconstruction curves\n' \
    "$MEASUREMENTS_ROOT" >&2
fi

# Loom contributes four VCs, too few for a coverage bar or curve to say
# anything, so the paper reports Curated, Cashmere, Velvet, and PLean. The
# recorded inputs under benchmark-data keep every suite.
EXCLUDE=(--exclude-suite loom)

# The table and bar renderers write SVG by hand so they need no matplotlib, but
# the paper wants PDF. Convert after rendering rather than teaching that
# renderer a second output format. plot-time-coverage.py emits PDF directly.
svg_to_pdf() {
  local svg="$1"
  local pdf="${svg%.svg}.pdf"
  if command -v rsvg-convert >/dev/null 2>&1; then
    rsvg-convert -f pdf -o "$pdf" "$svg"
  elif command -v inkscape >/dev/null 2>&1; then
    inkscape "$svg" --export-type=pdf --export-filename="$pdf" \
      >/dev/null 2>&1
  else
    printf 'warning: no SVG-to-PDF converter found; %s stays SVG only\n' \
      "$svg" >&2
    printf 'install one with: brew install librsvg\n' >&2
    return 0
  fi
}

python3 "$SCRIPT_DIR/plot-benchmarks.py" \
  "${RUN_DIRS[@]}" \
  --out-dir "$OUT_DIR" \
  "${EXCLUDE[@]}" \
  --only tables \
  --only coverage \
  --only outcomes

if [[ "$HAVE_MODES" == "true" ]]; then
  python3 "$SCRIPT_DIR/plot-benchmarks.py" \
    "${RUN_DIRS[@]}" \
    --out-dir "$OUT_DIR" \
    "${EXCLUDE[@]}" \
    --only reconstruction \
    --only reconstruction-failures
fi

# The time figures need matplotlib, which the other renderers deliberately do
# not require. Skip them rather than failing the whole artifact render.
if python3 -c "import matplotlib" >/dev/null 2>&1; then
  python3 "$SCRIPT_DIR/plot-time-coverage.py" \
    "${RUN_DIRS[@]}" \
    --out-dir "$OUT_DIR" \
    "${EXCLUDE[@]}" \
    --only main \
    --only coverage-table

  # The reconstruction comparison needs lean-smt measured beside Crush's
  # Alethe and portfolio lanes on the same VCs, which is what the lane check
  # above established.
  if [[ "$HAVE_RECON" == "true" ]]; then
    python3 "$SCRIPT_DIR/plot-time-coverage.py" \
      "${RUN_DIRS[@]}" \
      --out-dir "$OUT_DIR" \
      "${EXCLUDE[@]}" \
      --only reconstruction \
      --only reconstruction-table
  fi

  # Replay telemetry lives with the Crush ablation, and the scatter is drawn
  # by the matplotlib renderer so it shares the coverage figures' typeface.
  if [[ "$HAVE_MODES" == "true" ]]; then
    python3 "$SCRIPT_DIR/plot-time-coverage.py" \
      "${RUN_DIRS[@]}" \
      --out-dir "$OUT_DIR" \
      "${EXCLUDE[@]}" \
      --only scaling \
      --only failures-table \
      --only phase-breakdown \
      --only pairwise-time
  fi
else
  # Name the interpreter. matplotlib is commonly installed into a different
  # python3 than the one first on PATH -- putting a solver's directory ahead of
  # a virtualenv is enough to swap it -- and "python3 -m pip install matplotlib"
  # then installs into the wrong one and changes nothing.
  SKIPPED_TIME_FIGURES=true
  printf 'warning: %s cannot import matplotlib; skipping the coverage-over-time figures\n' \
    "$(command -v python3)" >&2
  printf 'install it for that interpreter: %s -m pip install matplotlib\n' \
    "$(command -v python3)" >&2
fi

for svg in "$OUT_DIR"/*.svg; do
  [[ -f "$svg" ]] || continue
  svg_to_pdf "$svg"
done

printf 'Figures written to %s\n' "$OUT_DIR"
ls "$OUT_DIR"/*.pdf 2>/dev/null | sed 's/^/  /'

# Say what is missing next to what was produced. A warning printed hundreds of
# lines earlier, on stderr, reads as success once the file list scrolls past it.
if [[ "${SKIPPED_TIME_FIGURES:-false}" == "true" ]]; then
  printf '\nNOT drawn: coverage-over-time-<suite>.pdf and the other curve figures\n' >&2
  printf 'matplotlib is missing from %s; see the warning above\n' \
    "$(command -v python3)" >&2
fi
