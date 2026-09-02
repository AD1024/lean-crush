#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage:
  bash benchmark-crush-modes.sh \
    --case_study <all|LeanHammer|Velvet|Cashmere|PLean>
  bash benchmark-crush-modes.sh \
    --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    --resume <result-directory>
  bash benchmark-crush-modes.sh --plot_only <result-directory>
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  usage >&2
  exit 2
}

case_study=""
plot_only=""
resume_dir=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --case_study)
      [[ $# -ge 2 ]] || die "--case_study requires a value"
      [[ -z "$case_study" ]] || die "--case_study may only be specified once"
      case_study="$2"
      shift 2
      ;;
    --plot_only)
      [[ $# -ge 2 ]] || die "--plot_only requires a result directory"
      [[ -z "$plot_only" ]] || die "--plot_only may only be specified once"
      plot_only="$2"
      shift 2
      ;;
    --resume)
      [[ $# -ge 2 ]] || die "--resume requires a result directory"
      [[ -z "$resume_dir" ]] || die "--resume may only be specified once"
      resume_dir="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

plot_results() {
  local output_root="$1"
  python3 "$ROOT/scripts/plot-benchmarks.py" \
    "${result_dirs[@]}" \
    --out-dir "$output_root/artifacts" \
    --only tables \
    --only reconstruction \
    --only reconstruction-failures \
    --only phase-breakdown \
    --only alethe-replay-scaling
}

if [[ -n "$plot_only" ]]; then
  [[ -z "$case_study" && -z "$resume_dir" ]] ||
    die "--plot_only cannot be combined with --case_study or --resume"
  [[ -d "$plot_only" ]] || die "result directory not found: $plot_only"
  plot_only="$(cd "$plot_only" && pwd)"
  result_dirs=()
  if [[ -f "$plot_only/measurements.tsv" ]]; then
    result_dirs+=("$plot_only")
  else
    for name in leanhammer corpora velvet cashmere plean; do
      if [[ -f "$plot_only/$name/measurements.tsv" ]]; then
        result_dirs+=("$plot_only/$name")
      fi
    done
  fi
  [[ ${#result_dirs[@]} -gt 0 ]] ||
    die "no normalized Crush-mode results found under: $plot_only"
  plot_results "$plot_only"
  printf 'Plots regenerated: %s/artifacts\n' "$plot_only"
  exit 0
fi

case "$case_study" in
  all) case_study="all" ;;
  LeanHammer|leanhammer) case_study="LeanHammer" ;;
  Velvet|velvet) case_study="Velvet" ;;
  Cashmere|cashmere) case_study="Cashmere" ;;
  PLean|plean) case_study="PLean" ;;
  "") die "--case_study is required" ;;
  *) die "unknown case study: $case_study" ;;
esac

resume=false
if [[ -n "$resume_dir" ]]; then
  [[ -d "$resume_dir" ]] || die "result directory not found: $resume_dir"
  result_root="$(cd "$resume_dir" && pwd)"
  resume=true
else
  timestamp="$(date +%Y%m%d-%H%M%S)"
  result_root="$ROOT/BenchmarkResults/crush-modes-$timestamp"
  mkdir -p "$result_root"
fi
result_dirs=()

run_leanhammer() {
  local out="$result_root/leanhammer"
  PROFILES="crush-verify crush-core crush-alethe crush-portfolio" \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  MAX_HEARTBEATS=1000000 \
  MAX_RECURSION_DEPTH=1000000 \
  CRUSH_PROFILE=true \
  USE_MATHLIB_CACHE=true \
  RESUME="$resume" \
  OUT_DIR="$out" \
    "$ROOT/scripts/benchmark-leanhammer.sh"
  result_dirs+=("$out")
}

run_corpora() {
  local run_cashmere="$1"
  local run_velvet="$2"
  local out_name="$3"
  local out="$result_root/$out_name"
  RUN_LEANHAMMER=false \
  RUN_LOOM=false \
  RUN_CASHMERE="$run_cashmere" \
  RUN_VELVET="$run_velvet" \
  RUN_AUTO=false \
  RUN_DUPER=false \
  RUN_CRUSH=true \
  RUN_GRIND=false \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  CRUSH_MODES="verify core alethe portfolio" \
  MAX_HEARTBEATS=1000000 \
  MAX_RECURSION_DEPTH=1000000 \
  CRUSH_PROFILE=true \
  USE_MATHLIB_CACHE=true \
  RESUME="$resume" \
  OUT_DIR="$out" \
    "$ROOT/scripts/benchmark-corpora.sh"
  result_dirs+=("$out")
}

run_plean() {
  local out="$result_root/plean"
  RUN_AUTO=false \
  RUN_DUPER=false \
  RUN_CRUSH=true \
  RUN_GRIND=false \
  PREPARE_TREES=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  CRUSH_MODES="verify core alethe portfolio" \
  MAX_HEARTBEATS=1000000 \
  MAX_RECURSION_DEPTH=1000000 \
  CRUSH_INST_FUEL=0 \
  CRUSH_PROFILE=true \
  USE_MATHLIB_CACHE=true \
  RESUME="$resume" \
  OUT_DIR="$out" \
    "$ROOT/scripts/benchmark-plean.sh"
  result_dirs+=("$out")
}

printf 'Running Crush-mode study for %s\n' "$case_study"
printf 'Results: %s\n' "$result_root"
if [[ "$resume" == "true" ]]; then
  printf 'Resuming from completed per-case checkpoints\n'
fi

case "$case_study" in
  LeanHammer)
    run_leanhammer
    ;;
  Velvet)
    run_corpora false true velvet
    ;;
  Cashmere)
    run_corpora true false cashmere
    ;;
  PLean)
    run_plean
    ;;
  all)
    run_leanhammer
    run_corpora true true corpora
    run_plean
    ;;
esac

plot_results "$result_root"

printf 'Crush-mode comparison complete: %s\n' "$result_root"
