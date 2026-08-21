#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_ROOT="${PAPER_DATA_ROOT:-scripts/benchmark-data}"
OUT_DIR="${1:-BenchmarkResults/figures}"

MAIN_ROOT="$DATA_ROOT/main"
MODES_ROOT="$DATA_ROOT/crush-modes"

cd "$CRUSH_ROOT"

for directory in \
    "$MAIN_ROOT/corpora" \
    "$MAIN_ROOT/leanhammer" \
    "$MAIN_ROOT/plean" \
    "$MODES_ROOT/corpora" \
    "$MODES_ROOT/leanhammer" \
    "$MODES_ROOT/plean"; do
  if [[ ! -d "$directory" ]]; then
    printf 'error: paper artifact data not found: %s\n' "$directory" >&2
    exit 1
  fi
done

python3 "$SCRIPT_DIR/plot-benchmarks.py" \
  "$MAIN_ROOT/corpora" \
  "$MAIN_ROOT/leanhammer" \
  "$MAIN_ROOT/plean" \
  --out-dir "$OUT_DIR" \
  --only tables \
  --only coverage \
  --only outcomes

python3 "$SCRIPT_DIR/plot-benchmarks.py" \
  "$MODES_ROOT/corpora" \
  "$MODES_ROOT/leanhammer" \
  "$MODES_ROOT/plean" \
  --out-dir "$OUT_DIR" \
  --only reconstruction \
  --only reconstruction-failures \
  --only phase-breakdown \
  --only alethe-replay-scaling
