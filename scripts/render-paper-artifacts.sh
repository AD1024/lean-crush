#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_ROOT="${PAPER_DATA_ROOT:-scripts/benchmark-data}"
OUT_DIR="${1:-BenchmarkResults/figures}"

# Each measurement's root is overridable so the figures can be rendered from a
# fresh run without renaming anything: `benchmark.sh --case_study all` writes
# `corpora/`, `leanhammer/` and `plean/` under one timestamped directory, which
# is exactly the shape MAIN_ROOT wants, and `benchmark-crush-modes.sh` does the
# same for MODES_ROOT.
MAIN_ROOT="${MAIN_ROOT:-$DATA_ROOT/main}"
MODES_ROOT="${MODES_ROOT:-$DATA_ROOT/crush-modes}"

cd "$CRUSH_ROOT"

# The reconstruction comparison's inputs ship as a zip rather than ~40 loose
# TSVs, so regenerating them is one binary change instead of a directory-wide
# add/delete churn. Unpack to a scratch directory when the caller has not
# pointed RECONSTRUCTION_ROOT at a run of their own.
RECONSTRUCTION_ARCHIVE="${RECONSTRUCTION_ARCHIVE:-$DATA_ROOT/reconstruction.zip}"
if [[ -z "${RECONSTRUCTION_ROOT:-}" && -f "$RECONSTRUCTION_ARCHIVE" ]]; then
  if command -v unzip >/dev/null 2>&1; then
    RECONSTRUCTION_UNPACKED="$(mktemp -d)"
    trap 'rm -rf "$RECONSTRUCTION_UNPACKED"' EXIT
    if unzip -q "$RECONSTRUCTION_ARCHIVE" -d "$RECONSTRUCTION_UNPACKED"; then
      RECONSTRUCTION_ROOT="$RECONSTRUCTION_UNPACKED"
    else
      printf 'warning: could not unpack %s; skipping the reconstruction figures\n' \
        "$RECONSTRUCTION_ARCHIVE" >&2
    fi
  else
    printf 'warning: unzip not found; skipping the reconstruction figures\n' >&2
  fi
fi

for directory in \
    "$MAIN_ROOT/corpora" \
    "$MAIN_ROOT/leanhammer" \
    "$MAIN_ROOT/plean" \
    "$MODES_ROOT/corpora" \
    "$MODES_ROOT/leanhammer" \
    "$MODES_ROOT/plean"; do
  if [[ ! -d "$directory" ]]; then
    printf 'error: paper artifact data not found: %s\n' "$directory" >&2
    printf 'point MAIN_ROOT / MODES_ROOT at your own run directories, e.g.\n' >&2
    printf '  MAIN_ROOT=BenchmarkResults/<main-run> \\\n' >&2
    printf '  MODES_ROOT=BenchmarkResults/<crush-modes-run> \\\n' >&2
    printf '  scripts/render-paper-artifacts.sh out/\n' >&2
    exit 1
  fi
done

# Loom contributes four VCs, too few for a coverage bar or curve to say
# anything, so the paper reports LeanHammer, Cashmere, Velvet, and PLean. The
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
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$OUT_DIR" \
  "${EXCLUDE[@]}" \
  --only tables \
  --only coverage \
  --only outcomes

python3 "$SCRIPT_DIR/plot-benchmarks.py" \
  "$MODES_ROOT/corpora" \
  "$MODES_ROOT/leanhammer" \
  "$MODES_ROOT/plean" \
  --out-dir "$OUT_DIR" \
  "${EXCLUDE[@]}" \
  --only reconstruction \
  --only reconstruction-failures \
  --only phase-breakdown

# The time figures need matplotlib, which the other renderers deliberately do
# not require. Skip them rather than failing the whole artifact render.
if python3 -c "import matplotlib" >/dev/null 2>&1; then
  python3 "$SCRIPT_DIR/plot-time-coverage.py" \
    "$MAIN_ROOT/corpora" \
    "$MAIN_ROOT/leanhammer" \
    "$MAIN_ROOT/plean" \
    --out-dir "$OUT_DIR" \
    "${EXCLUDE[@]}" \
    --only main \
    --only coverage-table

  # The reconstruction comparison needs a run that measured lean-smt beside
  # Crush's Alethe and portfolio lanes. RECONSTRUCTION_ROOT names it; the
  # recorded crush-modes data cannot stand in, since it has no lean-smt lane.
  if [[ -n "${RECONSTRUCTION_ROOT:-}" ]]; then
    python3 "$SCRIPT_DIR/plot-time-coverage.py" \
      "$RECONSTRUCTION_ROOT"/* \
      --out-dir "$OUT_DIR" \
      "${EXCLUDE[@]}" \
      --only reconstruction \
      --only reconstruction-table
  fi

  # Replay telemetry lives with the Crush ablation, and the scatter is drawn
  # by the matplotlib renderer so it shares the coverage figures' typeface.
  python3 "$SCRIPT_DIR/plot-time-coverage.py" \
    "$MODES_ROOT/corpora" \
    "$MODES_ROOT/leanhammer" \
    "$MODES_ROOT/plean" \
    --out-dir "$OUT_DIR" \
    "${EXCLUDE[@]}" \
    --only scaling
else
  printf 'warning: matplotlib is unavailable; skipping the time figures\n' >&2
  printf 'install it with: python3 -m pip install matplotlib\n' >&2
fi

for svg in "$OUT_DIR"/*.svg; do
  [[ -f "$svg" ]] || continue
  svg_to_pdf "$svg"
done

printf 'Figures written to %s\n' "$OUT_DIR"
ls "$OUT_DIR"/*.pdf 2>/dev/null | sed 's/^/  /'
