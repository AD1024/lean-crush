#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage:
  bash benchmark-reconstruction.sh \
    --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    [--smt_trees <directory>]
  bash benchmark-reconstruction.sh \
    --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    --resume <result-directory>
  bash benchmark-reconstruction.sh \
    --case_study <LeanHammer|Velvet|Cashmere|PLean> \
    --cases "<file> <file> ..."
  bash benchmark-reconstruction.sh --plot_only <result-directory> \
    [--exclude_suite <corpus>]

Compares checked proof reconstruction between lean-smt, Crush's strict Alethe
replay, and Crush's reconstruction portfolio. Only the pinned LeanHammer tree
requires lean-smt already; the other corpora get it from a recorded patch under
scripts/patches. Each lean-smt tree carries its corpus's Mathlib build plus
lean-smt's, so --smt_trees names a directory to keep them in between runs.

--exclude_suite omits a corpus from every table and figure; repeat it to omit
several. The published figures pass --exclude_suite loom.

--cases restricts the run to the named case-study files, relative to the corpus
root. It needs a single --case_study, since the file names are per corpus. Use
it to validate a lane before committing to a full run; the result is a subset,
not the published measurement.
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
smt_trees=""
cases=""
exclude_suites=()
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
    --smt_trees)
      [[ $# -ge 2 ]] || die "--smt_trees requires a directory"
      [[ -z "$smt_trees" ]] || die "--smt_trees may only be specified once"
      smt_trees="$2"
      shift 2
      ;;
    --exclude_suite)
      [[ $# -ge 2 ]] || die "--exclude_suite requires a corpus name"
      exclude_suites+=(--exclude-suite "$2")
      shift 2
      ;;
    --cases)
      [[ $# -ge 2 ]] || die "--cases requires a space-separated list of files"
      [[ -z "$cases" ]] || die "--cases may only be specified once"
      cases="$2"
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
    ${exclude_suites[@]+"${exclude_suites[@]}"} \
    --only tables \
    --only reconstruction \
    --only reconstruction-comparison \
    --only reconstruction-failures \
    --only alethe-replay-scaling
  # The reconstruction-over-time figure needs matplotlib, which the other
  # renderers deliberately do not require.
  if python3 -c "import matplotlib" >/dev/null 2>&1; then
    python3 "$ROOT/scripts/plot-time-coverage.py" \
      "${result_dirs[@]}" \
      --out-dir "$output_root/artifacts" \
      ${exclude_suites[@]+"${exclude_suites[@]}"} \
      --only reconstruction
  else
    # Name the interpreter: matplotlib is easily present in one python3 and
    # absent from another, and a bare `python3 -m pip install` then installs
    # into the wrong one and changes nothing.
    printf 'warning: %s cannot import matplotlib; skipping the time figure\n' \
      "$(command -v python3)" >&2
    printf 'install it for that interpreter: %s -m pip install matplotlib\n' \
      "$(command -v python3)" >&2
  fi
}

if [[ -n "$plot_only" ]]; then
  [[ -z "$case_study" && -z "$resume_dir" ]] ||
    die "--plot_only cannot be combined with --case_study or --resume"
  [[ -z "$smt_trees" ]] || die "--plot_only cannot be combined with --smt_trees"
  [[ -z "$cases" ]] || die "--plot_only cannot be combined with --cases"
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
    die "no normalized reconstruction results found under: $plot_only"
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
if [[ -n "$smt_trees" ]]; then
  mkdir -p "$smt_trees"
  smt_trees="$(cd "$smt_trees" && pwd)"
fi
if [[ -n "$cases" && "$case_study" == "all" ]]; then
  die "--cases needs a single --case_study; the file names are per corpus"
fi

resume=false
if [[ -n "$resume_dir" ]]; then
  [[ -d "$resume_dir" ]] || die "result directory not found: $resume_dir"
  result_root="$(cd "$resume_dir" && pwd)"
  resume=true
else
  timestamp="$(date +%Y%m%d-%H%M%S)"
  result_root="$ROOT/BenchmarkResults/reconstruction-$timestamp"
  mkdir -p "$result_root"
fi
result_dirs=()

run_leanhammer() {
  local out="$result_root/leanhammer"
  # crush-verify establishes the SMT-`unsat` cohort that the narrower
  # certificate-replay columns are measured against.
  PROFILES="crush-verify crush-alethe crush-portfolio smt-only" \
  HAMMER_CASES="$cases" \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
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
  local cashmere_cases=""
  local velvet_cases=""
  if [[ "$run_cashmere" == "true" ]]; then
    cashmere_cases="$cases"
  fi
  if [[ "$run_velvet" == "true" ]]; then
    velvet_cases="$cases"
  fi
  RUN_LEANHAMMER=false \
  CASHMERE_CASES="$cashmere_cases" \
  VELVET_CASES="$velvet_cases" \
  RUN_LOOM=false \
  RUN_CASHMERE="$run_cashmere" \
  RUN_VELVET="$run_velvet" \
  RUN_AUTO=false \
  RUN_DUPER=false \
  RUN_GRIND=false \
  RUN_CRUSH=true \
  RUN_SMT=true \
  CRUSH_MODES="verify alethe portfolio" \
  SMT_TREE_ROOT="$smt_trees" \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
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
  PLEAN_CASES="$cases" \
  RUN_AUTO=false \
  RUN_DUPER=false \
  RUN_GRIND=false \
  RUN_CRUSH=true \
  RUN_SMT=true \
  CRUSH_MODES="verify alethe portfolio" \
  SMT_TREE_ROOT="$smt_trees" \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
  PREPARE_TREES=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  CRUSH_INST_FUEL=0 \
  MAX_HEARTBEATS=1000000 \
  MAX_RECURSION_DEPTH=1000000 \
  CRUSH_PROFILE=true \
  USE_MATHLIB_CACHE=true \
  RESUME="$resume" \
  OUT_DIR="$out" \
    "$ROOT/scripts/benchmark-plean.sh"
  result_dirs+=("$out")
}

printf 'Running reconstruction comparison for %s\n' "$case_study"
printf 'Results: %s\n' "$result_root"
if [[ "$resume" == "true" ]]; then
  printf 'Resuming from completed per-case checkpoints\n'
fi

case "$case_study" in
  LeanHammer) run_leanhammer ;;
  Velvet) run_corpora false true velvet ;;
  Cashmere) run_corpora true false cashmere ;;
  PLean) run_plean ;;
  all)
    run_leanhammer
    run_corpora true true corpora
    run_plean
    ;;
esac

plot_results "$result_root"

printf 'Reconstruction comparison complete: %s\n' "$result_root"
