#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage:
  bash benchmark.sh --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    --with <crush|auto|duper|grind>
  bash benchmark.sh --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    --with <crush|auto|duper|grind> --resume <result-directory>
  bash benchmark.sh --plot_only <result-directory>
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  usage >&2
  exit 2
}

case_study=""
backend=""
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
    --with)
      [[ $# -ge 2 ]] || die "--with requires a value"
      [[ -z "$backend" ]] || die "--with may only be specified once"
      backend="$2"
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
    --only coverage \
    --only outcomes
}

if [[ -n "$plot_only" ]]; then
  [[ -z "$case_study" && -z "$backend" && -z "$resume_dir" ]] ||
    die "--plot_only cannot be combined with --case_study, --with, or --resume"
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
    die "no normalized benchmark results found under: $plot_only"
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

run_auto=false
run_duper=false
run_crush=false
run_grind=false
case "$backend" in
  auto) run_auto=true; leanhammer_profile="auto-duper" ;;
  duper) run_duper=true; leanhammer_profile="duper-only" ;;
  crush) run_crush=true; leanhammer_profile="crush-verify" ;;
  grind) run_grind=true; leanhammer_profile="grind-only" ;;
  "") die "--with is required" ;;
  *) die "unknown backend: $backend" ;;
esac

resume=false
if [[ -n "$resume_dir" ]]; then
  [[ -d "$resume_dir" ]] || die "result directory not found: $resume_dir"
  result_root="$(cd "$resume_dir" && pwd)"
  resume=true
else
  timestamp="$(date +%Y%m%d-%H%M%S)"
  result_root="$ROOT/BenchmarkResults/reproduction-$timestamp-$backend"
  mkdir -p "$result_root"
fi
result_dirs=()

run_leanhammer() {
  local out="$result_root/leanhammer"
  PROFILES="$leanhammer_profile" \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  DUPER_TIMEOUT=5 \
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
  RUN_AUTO="$run_auto" \
  RUN_DUPER="$run_duper" \
  RUN_CRUSH="$run_crush" \
  RUN_GRIND="$run_grind" \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  DUPER_TIMEOUT=5 \
  CRUSH_MODES=verify \
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
  RUN_AUTO="$run_auto" \
  RUN_DUPER="$run_duper" \
  RUN_CRUSH="$run_crush" \
  RUN_GRIND="$run_grind" \
  PREPARE_TREES=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  CRUSH_MODES=verify \
  MAX_HEARTBEATS=1000000 \
  MAX_RECURSION_DEPTH=1000000 \
  CRUSH_INST_FUEL=0 \
  DUPER_TIMEOUT=1 \
  DUPER_MAX_HEARTBEATS=20000 \
  DUPER_FILE_CPU_SECONDS=0 \
  GRIND_SPLITS=20 \
  CRUSH_PROFILE=true \
  USE_MATHLIB_CACHE=true \
  RESUME="$resume" \
  OUT_DIR="$out" \
    "$ROOT/scripts/benchmark-plean.sh"
  result_dirs+=("$out")
}

printf 'Running %s with %s\n' "$case_study" "$backend"
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

printf 'Benchmark reproduction complete: %s\n' "$result_root"
