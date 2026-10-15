#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage:
  bash run-experiments.sh [--out <dir>] [--resume <dir>] [--suites "<name> ..."]
                          [--skip_figures] [--figures_only <dir>] [--update_archive]

Measures every lane every published figure and table needs, into one dataset,
and draws them. This is the whole experiment: there is nothing to merge
afterwards and no second study to reconcile against.

One dataset is the point. The lanes used to be split across three overlapping
runs, and because a (suite, lane) could appear in more than one of them, the
copies drifted -- Velvet's Alethe rows were post-fix in one and pre-fix in
another, so a figure said 239 checked VCs while the prose said 196. Here each
(suite, lane) is measured once and cannot disagree with itself.

Output layout, which is what the renderer reads:

  <dir>/curated/     the curated obligations, one backend per suite branch
  <dir>/corpora/     Loom, Cashmere and Velvet
  <dir>/plean/       PLean
  <dir>/figures/     every figure and table

Lanes, per suite: Auto, Duper, `grind`, lean-smt, and Crush trusted, strict
Alethe and portfolio. Together these cover the coverage comparison, the
outcome breakdown, the reconstruction study, the cross-tool comparison against
lean-smt, the phase breakdown and the replay-scaling scatter.

Options:
  --out <dir>          where to write (default: BenchmarkResults/experiments-<stamp>)
  --resume <dir>       continue into an existing dataset, skipping finished cases
  --suites "<names>"   subset of: curated corpora plean (default: all three)
  --plean-config <file> optional prepared shared PLean environment (JSON).
                       Otherwise setup is automatic under <dir>/plean-environment.
                       Resume reuses <dir>/plean/config.json.
  --skip_figures       measure and generate reports, without plotting
  --figures_only <dir> regenerate reports and redraw, measuring nothing
  --update_archive     also refresh scripts/benchmark-data/eval-data.zip from the run
  --keep_trees         retain managed builds for reuse in future runs.
                       Otherwise release each build after its last consumer.
                       PLean sources, logs and checkpoints are always retained;
                       externally supplied environments are never removed.
  --require-cache      stop if a corpus cannot fetch its Mathlib build cache,
                       rather than falling back to a source build. A miss is
                       not a correctness problem -- the build produces the
                       same artifacts -- and on a platform with no cached
                       build the fallback is the only way to run at all, so
                       it is the default. Use this when you know the cache
                       should be there and would rather fail in the first
                       minute than find a multi-hour build later.

Environment:
  REPEATS          repeats per VC. One, for every case study, which is what
                   the published numbers use. Coverage is deterministic except
                   at the solver cap, where a VC that finishes near the limit
                   can land either side of it between runs.
  SOLVER           cvc5 (default). lean-smt drives cvc5 through in-process
                   bindings and cannot run under z3, so the smt lane pins it.
  TIMEOUT          per-query solver seconds (default 5)
  CRUSH_MODES      Crush lanes (default "verify alethe portfolio"; add "core"
                   to fill the Core column, which doubles the Crush work)
  Z3_BIN, CVC5_BIN pin solver binaries when PATH would pick the wrong one
  CURATED_TREES    where the curated suite's per-branch builds live
  SMT_TREE_ROOT    where the lean-smt corpus worktrees live
  PLEAN_SHARED_CONFIG  default for --plean-config. PLean uses the audited shared
                   scaffold, including lean-smt; no legacy harness fallback.
                   Its fixed settings are one repeat, 5s solver timeout,
                   1,000,000 heartbeats/recursion depth, and Crush trusted,
                   Alethe and portfolio modes. Auto retains Lean 4.24.0.

Use stable tree paths with --keep_trees to reuse builds across runs. Within a
run, all modes sharing a build finish before it is released. Builds from
different revisions/toolchains remain separate.

Examples:
  bash run-experiments.sh
  bash run-experiments.sh --out BenchmarkResults/paper --update_archive
  bash run-experiments.sh --suites curated
  bash run-experiments.sh --figures_only BenchmarkResults/experiments-<stamp>
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  usage >&2
  exit 2
}

out_dir=""
resume_dir=""
figures_only=""
skip_figures=false
update_archive=false
require_cache=false
keep_trees=false
suites="curated corpora plean"
plean_config="${PLEAN_SHARED_CONFIG:-}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out) [[ $# -ge 2 ]] || die "--out requires a directory"
      out_dir="$2"; shift 2 ;;
    --resume) [[ $# -ge 2 ]] || die "--resume requires a directory"
      resume_dir="$2"; shift 2 ;;
    --figures_only) [[ $# -ge 2 ]] || die "--figures_only requires a directory"
      figures_only="$2"; shift 2 ;;
    --suites) [[ $# -ge 2 ]] || die "--suites requires a value"
      suites="$2"; shift 2 ;;
    --plean-config) [[ $# -ge 2 ]] || die "--plean-config requires a file"
      plean_config="$2"; shift 2 ;;
    --skip_figures) skip_figures=true; shift ;;
    --update_archive) update_archive=true; shift ;;
    --require-cache) require_cache=true; shift ;;
    --keep_trees) keep_trees=true; shift ;;
    -h|--help) usage; exit 0 ;;
    *) die "unknown option: $1" ;;
  esac
done

REPEATS="${REPEATS:-1}"
SOLVER="${SOLVER:-cvc5}"
TIMEOUT="${TIMEOUT:-5}"
# `core` is omitted by default: it is a second full Crush pass whose column the
# published tables report as unmeasured.
CRUSH_MODES="${CRUSH_MODES:-verify alethe portfolio}"
MAX_HEARTBEATS="${MAX_HEARTBEATS:-1000000}"
MAX_RECURSION_DEPTH="${MAX_RECURSION_DEPTH:-1000000}"
DUPER_TIMEOUT="${DUPER_TIMEOUT:-5}"
REQUIRE_MATHLIB_CACHE="${REQUIRE_MATHLIB_CACHE:-false}"
source_cache_dir="${BENCHMARK_SOURCE_CACHE:-$ROOT/BenchmarkResults/sources}"
CURATED_TREES="${CURATED_TREES:-$ROOT/BenchmarkResults/curated-trees}"
SMT_TREE_ROOT="${SMT_TREE_ROOT:-$ROOT/BenchmarkResults/trees}"

# lean-smt reaches cvc5 through in-process bindings, so it ignores SOLVER and
# cannot run under z3. Refuse rather than record a lane under a solver it never
# used.
if [[ "$SOLVER" != "cvc5" ]]; then
  die "the lean-smt lane requires SOLVER=cvc5; got $SOLVER"
fi

refresh_reports() {
  local root="$1" group
  for group in curated corpora plean; do
    [[ -f "$root/$group/measurements.tsv" ]] || continue
    python3 "$ROOT/scripts/benchmark-report.py" \
      --measurements "$root/$group/measurements.tsv" \
      --profiles "$root/$group/profile-events.tsv" \
      --out-dir "$root/$group" --require-uniform-headline
  done
}

draw_figures() {
  local root="$1"
  refresh_reports "$root"
  printf '\n=== figures ===\n'
  MEASUREMENTS_ROOT="$root" \
    bash "$ROOT/scripts/render-paper-artifacts.sh" "$root/figures"
}

pack_archive() {
  local root="$1"
  local archive="$ROOT/scripts/benchmark-data/eval-data.zip"
  local staging
  staging="$(mktemp -d "${TMPDIR:-/tmp}/eval-data.XXXXXX")"
  local group
  for group in curated corpora plean; do
    [[ -d "$root/$group" ]] || continue
    mkdir -p "$staging/$group"
    # Measurements and the reports regenerated from them. Logs and generated
    # sources are run scratch, not data.
    cp "$root/$group"/*.tsv "$staging/$group/" 2>/dev/null || true
    rm -f "$staging/$group/checkpoints.tsv"
  done
  rm -f "$archive"
  (cd "$staging" && zip -rq "$archive" .)
  rm -rf "$staging"
  printf 'Archive refreshed: %s\n' "$archive"
}

if [[ -n "$figures_only" ]]; then
  [[ -z "$out_dir" && -z "$resume_dir" ]] ||
    die "--figures_only cannot be combined with --out or --resume"
  [[ -d "$figures_only" ]] || die "dataset not found: $figures_only"
  figures_only="$(cd "$figures_only" && pwd)"
  draw_figures "$figures_only"
  [[ "$update_archive" == "true" ]] && pack_archive "$figures_only"
  exit 0
fi

resume=false
if [[ -n "$resume_dir" ]]; then
  [[ -z "$out_dir" ]] || die "--resume cannot be combined with --out"
  [[ -d "$resume_dir" ]] || die "dataset not found: $resume_dir"
  dataset="$(cd "$resume_dir" && pwd)"
  resume=true
else
  dataset="${out_dir:-$ROOT/BenchmarkResults/experiments-$(date +%Y%m%d-%H%M%S)}"
  mkdir -p "$dataset"
  dataset="$(cd "$dataset" && pwd)"
fi

run_suite() {
  local name="$1"
  local want
  for want in $suites; do
    [[ "$want" == "$name" ]] && return 0
  done
  return 1
}

# Validate the PLean selection before building or measuring any suite. The
# shared runner deliberately fixes these options for cross-backend fairness;
# reject overrides rather than silently ignore them.
if run_suite plean; then
  [[ "$REPEATS" == 1 && "$TIMEOUT" == 5 && "$DUPER_TIMEOUT" == 5 &&
     "$MAX_HEARTBEATS" == 1000000 && "$MAX_RECURSION_DEPTH" == 1000000 &&
     "${GRIND_SPLITS:-20}" == 20 && "${SMT_TIMEOUT:-5}" == 5 &&
     "${SMT_MONO:-true}" == true && "${CRUSH_INST_FUEL:-0}" == 0 ]] ||
    die "shared PLean requires the fixed benchmark settings listed in --help"
  [[ "$(printf '%s\n' $CRUSH_MODES | LC_ALL=C sort | tr '\n' ' ')" == "alethe portfolio verify " ]] ||
    die "shared PLean requires CRUSH_MODES='verify alethe portfolio'"
  if [[ "$resume" == true && -d "$dataset/plean" ]]; then
    [[ -f "$dataset/plean/scaffold-audit.json" && -f "$dataset/plean/config.json" ]] ||
      die "cannot resume legacy PLean results; use a fresh dataset for the shared harness"
    if [[ -n "$plean_config" ]]; then
      python3 - "$plean_config" "$dataset/plean/config.json" <<'PY' ||
import json
from pathlib import Path
import sys
if json.loads(Path(sys.argv[1]).read_text()) != json.loads(Path(sys.argv[2]).read_text()):
    sys.exit('PLean environment differs from the recorded run')
PY
        die "resume must use the recorded PLean environment"
    fi
    plean_config="$dataset/plean/config.json"
  fi
  if [[ "$resume" == false && -e "$dataset/plean" ]]; then
    die "PLean output already exists; use --resume or a fresh dataset"
  fi
  if [[ -n "$plean_config" ]]; then
    [[ -f "$plean_config" ]] || die "PLean config not found: $plean_config"
    plean_config="$(cd "$(dirname "$plean_config")" && pwd)/$(basename "$plean_config")"
  fi
fi

reclaim_build_trees=true
[[ "$keep_trees" == false ]] || reclaim_build_trees=false
# Every suite checks individual trees against these future dependencies;
# never recursively delete a cache root containing caller-owned builds.
export BENCHMARK_KEEP_PLEAN_CONFIG="$plean_config"

printf 'Dataset: %s\n' "$dataset"
printf 'Suites:  %s\n' "$suites"
printf 'Lanes:   auto duper grind lean-smt %s\n' \
  "$(printf 'crush-%s ' $CRUSH_MODES)"
printf 'Repeats: %s, solver %s, timeout %ss\n' "$REPEATS" "$SOLVER" "$TIMEOUT"
if [[ "$require_cache" == "true" ]]; then
  REQUIRE_MATHLIB_CACHE=true
  printf 'Cache:   required; a miss stops the run\n'
else
  printf 'Cache:   preferred; a miss falls back to a source build (hours)\n'
fi
export REQUIRE_MATHLIB_CACHE
printf '\n'

# PLean consumes its prepared builds without mutating them. The other suites
# retain their existing build workflow.
if run_suite curated || run_suite corpora; then
  printf 'Building local Crush\n'
  (cd "$ROOT" && lake build Crush) > "$dataset/build-crush.log" 2>&1 || {
    tail -n 80 "$dataset/build-crush.log" >&2
    die "local Crush build failed"
  }
fi

# The curated suite keeps one backend per branch, so its lanes are named
# directly rather than through RUN_* switches.
if run_suite curated; then
  printf '\n=== curated ===\n'
  curated_profiles="smt-only grind-only duper-only auto-smt"
  for mode in $CRUSH_MODES; do
    curated_profiles="crush-$mode $curated_profiles"
  done
  PROFILES="$curated_profiles" \
  CURATED_TREES="$CURATED_TREES" \
  RECLAIM_BUILD_TREES="$reclaim_build_trees" \
  REPEATS="$REPEATS" SOLVER="$SOLVER" TIMEOUT="$TIMEOUT" \
  SMT_TIMEOUT=5 SMT_MONO=true DUPER_TIMEOUT="$DUPER_TIMEOUT" \
  MAX_HEARTBEATS="$MAX_HEARTBEATS" MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
  CRUSH_PROFILE=true \
  RESUME="$resume" OUT_DIR="$dataset/curated" \
    bash "$ROOT/scripts/benchmark-curated.sh"
fi

if run_suite corpora; then
  printf '\n=== corpora (Loom, Cashmere, Velvet) ===\n'
  # Shared Crush/grind and Loom/Cashmere consumers finish before cleanup.
  RUN_CURATED=false \
  RUN_AUTO=true RUN_DUPER=true RUN_CRUSH=true RUN_GRIND=true RUN_SMT=true \
  KEEP_WORKTREES="$keep_trees" RECLAIM_BUILD_TREES="$reclaim_build_trees" \
  CRUSH_MODES="$CRUSH_MODES" \
  SMT_TREE_ROOT="$SMT_TREE_ROOT" \
  REPEATS="$REPEATS" SOLVER="$SOLVER" TIMEOUT="$TIMEOUT" \
  DUPER_TIMEOUT="$DUPER_TIMEOUT" \
  MAX_HEARTBEATS="$MAX_HEARTBEATS" MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
  CRUSH_PROFILE=true \
  RESUME="$resume" OUT_DIR="$dataset/corpora" \
    bash "$ROOT/scripts/benchmark-corpora.sh"
fi

if run_suite plean; then
  printf '\n=== plean ===\n'
  plean_environment="$dataset/plean-environment"
  plean_cleanup_args=()
  # Provision only when this suite is reached: other suites may reclaim their
  # independent build trees first. Never reprovision a recorded resume.
  if [[ -z "$plean_config" ]]; then
    plean_setup_args=()
    if [[ "$REQUIRE_MATHLIB_CACHE" == true ]]; then
      plean_setup_args+=(--require-cache)
    fi
    python3 "$ROOT/scripts/setup-plean-shared.py" --out "$plean_environment" \
      ${plean_setup_args[@]+"${plean_setup_args[@]}"}
    plean_config="$plean_environment/run-config.json"
  fi
  # Only the automatically provisioned environment belongs to this dataset.
  # A resume records the same config under plean/config.json. Explicit
  # external environments remain caller-owned even after the final lane.
  if [[ "$keep_trees" == false && -f "$plean_environment/run-config.json" ]] &&
      python3 - "$plean_config" "$plean_environment/run-config.json" <<'PY'
import json
from pathlib import Path
import sys
sys.exit(json.loads(Path(sys.argv[1]).read_text()) != json.loads(Path(sys.argv[2]).read_text()))
PY
  then
    plean_cleanup_args=(--reclaim-builds "$plean_environment")
  fi
  plean_prepare_args=()
  if [[ "$resume" == true && -d "$dataset/plean" ]]; then
    plean_prepare_args+=(--resume)
  fi
  python3 "$ROOT/scripts/benchmark-plean-shared.py" \
    --config "$plean_config" --out "$dataset/plean" --prepare-only \
    ${plean_prepare_args[@]+"${plean_prepare_args[@]}"}
  python3 "$ROOT/scripts/benchmark-plean-shared.py" \
    --config "$plean_config" --out "$dataset/plean" --resume \
    ${plean_cleanup_args[@]+"${plean_cleanup_args[@]}"}
fi

if [[ "$skip_figures" == "true" ]]; then
  refresh_reports "$dataset"
  printf '\nMeasurement complete: %s\n' "$dataset"
  printf 'Draw the figures with --figures_only %s\n' "$dataset"
  exit 0
fi

draw_figures "$dataset"
[[ "$update_archive" == "true" ]] && pack_archive "$dataset"

printf '\nExperiments complete: %s\n' "$dataset"
