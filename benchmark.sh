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
  bash benchmark.sh --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
    --with lean-smt [--smt_trees <directory>]
  bash benchmark.sh --case_study <LeanHammer|Velvet|Cashmere|PLean> \
    --with <backend> --cases "<file> <file> ..."
  bash benchmark.sh --plot_only <result-directory> \
    [--exclude_suite <corpus>]

--with lean-smt measures ufmg-smite/lean-smt. Only the pinned LeanHammer tree
requires it already; for Velvet, Cashmere, and PLean the harness applies a
recorded patch from scripts/patches that adds the dependency (and, for PLean,
substitutes the backend inside its tactic module), then resolves it with
`lake update Smt` and verifies that no revision the corpus already pinned
moved. Each lean-smt tree carries its corpus's Mathlib build plus lean-smt's,
so --smt_trees names a directory to keep them in between runs; without it they
are temporary checkouts, rebuilt from the pinned revision every run.

--exclude_suite omits a corpus from every table and figure; repeat it to omit
several. The published figures pass --exclude_suite loom, whose four VCs are
too few for a coverage bar or a curve to say anything. The recorded TSVs always
keep every corpus.

--cases restricts the run to the named case-study files, relative to the corpus
root (for example: --cases "Examples/PingPongTrivial.lean"). It needs a single
--case_study, since the file names are per corpus. Use it to validate a lane
before committing to a full run; the result is a subset, not the published
measurement.
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
    --only coverage \
    --only outcomes
  # The time-versus-coverage figure needs matplotlib, which the other
  # renderers deliberately do not require. Skip it rather than failing the
  # whole plot step.
  if python3 -c "import matplotlib" >/dev/null 2>&1; then
    python3 "$ROOT/scripts/plot-time-coverage.py" \
      "${result_dirs[@]}" \
      --out-dir "$output_root/artifacts" \
      ${exclude_suites[@]+"${exclude_suites[@]}"} \
      --only main
  else
    printf 'warning: matplotlib is unavailable; skipping the time figure\n' >&2
    printf 'install it with: python3 -m pip install matplotlib\n' >&2
  fi
}

if [[ -n "$plot_only" ]]; then
  [[ -z "$case_study" && -z "$backend" && -z "$resume_dir" ]] ||
    die "--plot_only cannot be combined with --case_study, --with, or --resume"
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

# Crush answers two different questions, so the coverage comparison measures
# both and folds them into the same TSVs: `verify` trusts the solver's verdict,
# `portfolio` returns a kernel-checked Lean proof or nothing (Alethe replay
# first, then core-directed reconstruction). They surface as the `crush` and
# `crush-checked` headline backends. Narrow it to one mode to halve the Crush
# work, e.g. CRUSH_LANES=verify.
CRUSH_LANES="${CRUSH_LANES:-verify portfolio}"

run_auto=false
run_duper=false
run_crush=false
run_grind=false
run_smt=false
case "$backend" in
  auto) run_auto=true; leanhammer_profile="auto-duper" ;;
  duper) run_duper=true; leanhammer_profile="duper-only" ;;
  crush)
    run_crush=true
    # LeanHammer names lanes where the others name modes.
    leanhammer_profile="$(printf 'crush-%s ' $CRUSH_LANES)"
    leanhammer_profile="${leanhammer_profile% }"
    ;;
  grind) run_grind=true; leanhammer_profile="grind-only" ;;
  lean-smt|smt)
    backend="lean-smt"
    run_smt=true
    leanhammer_profile="smt-only"
    ;;
  "") die "--with is required" ;;
  *) die "unknown backend: $backend" ;;
esac
if [[ -n "$smt_trees" ]]; then
  [[ "$backend" == "lean-smt" ]] ||
    die "--smt_trees only applies to --with lean-smt"
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
  result_root="$ROOT/BenchmarkResults/reproduction-$timestamp-$backend"
  mkdir -p "$result_root"
fi
result_dirs=()

run_leanhammer() {
  local out="$result_root/leanhammer"
  PROFILES="$leanhammer_profile" \
  HAMMER_CASES="$cases" \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
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
  # --cases names files in one corpus, and it already required a single
  # --case_study, so at most one of these is non-empty.
  local cashmere_cases=""
  local velvet_cases=""
  if [[ "$run_cashmere" == "true" ]]; then
    cashmere_cases="$cases"
  fi
  if [[ "$run_velvet" == "true" ]]; then
    velvet_cases="$cases"
  fi
  RUN_LEANHAMMER=false \
  RUN_LOOM=false \
  RUN_CASHMERE="$run_cashmere" \
  RUN_VELVET="$run_velvet" \
  CASHMERE_CASES="$cashmere_cases" \
  VELVET_CASES="$velvet_cases" \
  RUN_AUTO="$run_auto" \
  RUN_DUPER="$run_duper" \
  RUN_CRUSH="$run_crush" \
  RUN_GRIND="$run_grind" \
  RUN_SMT="$run_smt" \
  SMT_TREE_ROOT="$smt_trees" \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  DUPER_TIMEOUT=5 \
  CRUSH_MODES="$CRUSH_LANES" \
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
  RUN_AUTO="$run_auto" \
  RUN_DUPER="$run_duper" \
  RUN_CRUSH="$run_crush" \
  RUN_GRIND="$run_grind" \
  RUN_SMT="$run_smt" \
  SMT_TREE_ROOT="$smt_trees" \
  SMT_TIMEOUT=5 \
  SMT_MONO=true \
  PREPARE_TREES=true \
  REPEATS=1 \
  SOLVER=cvc5 \
  TIMEOUT=5 \
  CRUSH_MODES="$CRUSH_LANES" \
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
