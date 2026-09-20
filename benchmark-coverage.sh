#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage:
  bash benchmark-coverage.sh --case_study <all|LeanHammer|Velvet|Cashmere|PLean>
  bash benchmark-coverage.sh --case_study <...> --resume <result-directory>
  bash benchmark-coverage.sh --case_study <...> --skip_figures
  bash benchmark-coverage.sh --figures_only <result-directory>
  bash benchmark-coverage.sh --case_study <one> --cases "<file> ..."

Runs every backend of the coverage comparison into one result directory, then
draws the figures from it. `benchmark.sh` measures one backend per invocation
and each into its own directory, which is right when you are iterating on a
single lane but leaves the cross-backend figures needing a directory that no
single invocation produces. This is the end-to-end path.

Crush is measured in both lanes, so the run yields the `crush` (SMT trusted)
and `crush-checked` (kernel-checked) series together. Override with CRUSH_LANES.

Environment:
  BACKENDS     backends to measure, in order
               (default: "crush auto duper grind lean-smt")
  CRUSH_LANES  Crush lanes to measure (default: "verify portfolio")
  SMT_TREES    directory to keep the lean-smt worktrees in between runs
  Z3_BIN       z3 to use; set it when a virtualenv shadows the intended one
  CVC5_BIN     cvc5 to use

--cases restricts the run to the named case-study files, as `benchmark.sh`
takes it, so it needs a single --case_study. Use it to check the whole path --
measure, report, draw -- in minutes before committing to a full run. The result
is a subset, not the published measurement.

Examples:
  # Everything, then figures.
  bash benchmark-coverage.sh --case_study all

  # Skip the slow lean-smt lane.
  BACKENDS="crush auto duper grind" bash benchmark-coverage.sh --case_study all

  # Redraw from a finished run without measuring anything.
  bash benchmark-coverage.sh --figures_only BenchmarkResults/coverage-<stamp>

  # Smoke-test the whole path on one file.
  BACKENDS=grind bash benchmark-coverage.sh --case_study Cashmere \
    --cases "Cashmere/Examples/Bits.lean"
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  usage >&2
  exit 2
}

BACKENDS="${BACKENDS:-crush auto duper grind lean-smt}"

case_study=""
resume_dir=""
figures_only=""
skip_figures=false
cases=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --case_study)
      [[ $# -ge 2 ]] || die "--case_study requires a value"
      [[ -z "$case_study" ]] || die "--case_study may only be specified once"
      case_study="$2"; shift 2 ;;
    --resume)
      [[ $# -ge 2 ]] || die "--resume requires a result directory"
      [[ -z "$resume_dir" ]] || die "--resume may only be specified once"
      resume_dir="$2"; shift 2 ;;
    --figures_only)
      [[ $# -ge 2 ]] || die "--figures_only requires a result directory"
      [[ -z "$figures_only" ]] || die "--figures_only may only be specified once"
      figures_only="$2"; shift 2 ;;
    --cases)
      [[ $# -ge 2 ]] || die "--cases requires a value"
      [[ -z "$cases" ]] || die "--cases may only be specified once"
      cases="$2"; shift 2 ;;
    --skip_figures)
      skip_figures=true; shift ;;
    -h|--help)
      usage; exit 0 ;;
    *)
      die "unknown option: $1" ;;
  esac
done

# Figures come from the same renderer the published artifacts use, so a run's
# figures and the committed ones cannot drift apart: same suite exclusions, same
# SVG-to-PDF step.
#
# Both other studies' roots are pointed at paths that do not exist, so the
# renderer skips their figures. Without that it would draw them from the
# committed archive, and a reader would find figures in their run directory that
# their run did not produce. They come from benchmark-crush-modes.sh and
# benchmark-reconstruction.sh respectively.
draw_figures() {
  local root="$1"
  printf '\nDrawing figures from %s\n' "$root"
  MAIN_ROOT="$root" \
  MODES_ROOT="$root/__no-crush-modes__" \
  RECONSTRUCTION_ROOT="$root/__no-reconstruction__" \
    bash "$ROOT/scripts/render-paper-artifacts.sh" "$root/figures"
}

if [[ -n "$figures_only" ]]; then
  [[ -z "$case_study" && -z "$resume_dir" ]] ||
    die "--figures_only cannot be combined with --case_study or --resume"
  [[ -d "$figures_only" ]] || die "result directory not found: $figures_only"
  draw_figures "$(cd "$figures_only" && pwd)"
  exit 0
fi

[[ -n "$case_study" ]] || die "--case_study is required"
# benchmark.sh rejects --cases with --case_study all, since the file names are
# per corpus; say so here rather than after the first backend has been built.
if [[ -n "$cases" && "$case_study" == "all" ]]; then
  die "--cases needs a single --case_study, not all"
fi

if [[ -n "$resume_dir" ]]; then
  [[ -d "$resume_dir" ]] || die "result directory not found: $resume_dir"
  result_root="$(cd "$resume_dir" && pwd)"
  resume_flag=(--resume "$result_root")
else
  result_root="$ROOT/BenchmarkResults/coverage-$(date +%Y%m%d-%H%M%S)"
  mkdir -p "$result_root"
  # Every backend after the first joins the directory the first one created, so
  # they land in the same corpora/leanhammer/plean TSVs and the figures can
  # compare them. Per-case checkpoints make this restartable too.
  resume_flag=(--resume "$result_root")
fi

printf 'Coverage comparison: %s\n' "$case_study"
printf 'Backends: %s\n' "$BACKENDS"
printf 'Results: %s\n' "$result_root"

for backend in $BACKENDS; do
  printf '\n=== %s ===\n' "$backend"
  smt_flag=()
  if [[ "$backend" == "lean-smt" && -n "${SMT_TREES:-}" ]]; then
    smt_flag=(--smt_trees "$SMT_TREES")
  fi
  cases_flag=()
  # `&&` as the last command would make the loop body exit non-zero under
  # `set -e` when no --cases was given, so this is a real if.
  if [[ -n "$cases" ]]; then
    cases_flag=(--cases "$cases")
  fi
  CRUSH_LANES="${CRUSH_LANES:-verify portfolio}" \
    bash "$ROOT/benchmark.sh" \
      --case_study "$case_study" \
      --with "$backend" \
      "${resume_flag[@]}" \
      ${smt_flag[@]+"${smt_flag[@]}"} \
      ${cases_flag[@]+"${cases_flag[@]}"}
done

if [[ "$skip_figures" == "true" ]]; then
  printf '\nCoverage comparison complete: %s\n' "$result_root"
  printf 'Figures skipped; draw them with --figures_only %s\n' "$result_root"
  exit 0
fi

draw_figures "$result_root"

printf '\nCoverage comparison complete: %s\n' "$result_root"
