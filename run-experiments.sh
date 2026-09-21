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
  --skip_figures       measure only
  --figures_only <dir> redraw a finished dataset, measuring nothing
  --update_archive     also refresh scripts/benchmark-data/eval-data.zip from the run
  --keep_trees         keep each suite's build trees instead of deleting them
                       once that suite is measured. Every lane gets its own
                       worktree carrying its own Mathlib, about 7GB each, and
                       thirteen of them do not fit on a typical disk -- so by
                       default a suite's trees are removed as soon as its
                       measurements are written, capping usage at one suite.
                       Keep them to make a later --resume cheap, if the disk
                       can take it.
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

Both tree directories are worth setting to a stable path: each holds a Lake
build, and keeping them between runs is the difference between minutes and
hours.

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

draw_figures() {
  local root="$1"
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

# A suite's trees are worth nothing once its measurements exist, and they are
# the only thing on disk at this scale: each carries its own Mathlib build.
# Removing them between suites is what keeps the peak at one suite's worth
# rather than the sum of all three.
reclaim_trees() {
  local what="$1"
  shift
  local freed path
  [[ "$keep_trees" == "true" ]] && return 0
  for path in "$@"; do
    [[ -d "$path" ]] || continue
    freed="$(du -sh "$path" 2>/dev/null | cut -f1)"
    # Worktrees are registered with their origin repository; pruning keeps that
    # registry from accumulating entries pointing at directories now gone.
    rm -rf "$path"
    printf 'Reclaimed %s of %s build trees (%s)\n' "${freed:-?}" "$what" "$path"
  done
  git -C "$ROOT" worktree prune >/dev/null 2>&1 || true
  if [[ -d "$source_cache_dir" ]]; then
    local repo
    for repo in "$source_cache_dir"/*/; do
      [[ -d "$repo" ]] || continue
      git -C "$repo" worktree prune >/dev/null 2>&1 || true
    done
  fi
}

run_suite() {
  local name="$1"
  local want
  for want in $suites; do
    [[ "$want" == "$name" ]] && return 0
  done
  return 1
}

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

printf 'Building local Crush\n'
(cd "$ROOT" && lake build Crush) > "$dataset/build-crush.log" 2>&1 || {
  tail -n 80 "$dataset/build-crush.log" >&2
  die "local Crush build failed"
}

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
  REPEATS="$REPEATS" SOLVER="$SOLVER" TIMEOUT="$TIMEOUT" \
  SMT_TIMEOUT=5 SMT_MONO=true DUPER_TIMEOUT="$DUPER_TIMEOUT" \
  MAX_HEARTBEATS="$MAX_HEARTBEATS" MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
  CRUSH_PROFILE=true \
  RESUME="$resume" OUT_DIR="$dataset/curated" \
    bash "$ROOT/scripts/benchmark-curated.sh"
  reclaim_trees curated "$CURATED_TREES"
fi

if run_suite corpora; then
  printf '\n=== corpora (Loom, Cashmere, Velvet) ===\n'
  RUN_CURATED=false \
  RUN_AUTO=true RUN_DUPER=true RUN_CRUSH=true RUN_GRIND=true RUN_SMT=true \
  CRUSH_MODES="$CRUSH_MODES" \
  SMT_TREE_ROOT="$SMT_TREE_ROOT" \
  REPEATS="$REPEATS" SOLVER="$SOLVER" TIMEOUT="$TIMEOUT" \
  DUPER_TIMEOUT="$DUPER_TIMEOUT" \
  MAX_HEARTBEATS="$MAX_HEARTBEATS" MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
  CRUSH_PROFILE=true \
  RESUME="$resume" OUT_DIR="$dataset/corpora" \
    bash "$ROOT/scripts/benchmark-corpora.sh"
  # The corpora harness removes its own temporary worktrees; the lean-smt trees
  # it is told to keep are the ones that survive, and PLean does not reuse them.
  reclaim_trees corpora "$SMT_TREE_ROOT"
fi

if run_suite plean; then
  printf '\n=== plean ===\n'
  RUN_AUTO=true RUN_DUPER=true RUN_CRUSH=true RUN_GRIND=true RUN_SMT=true \
  CRUSH_MODES="$CRUSH_MODES" \
  SMT_TREE_ROOT="$SMT_TREE_ROOT" \
  REPEATS="$REPEATS" SOLVER="$SOLVER" TIMEOUT="$TIMEOUT" \
  DUPER_TIMEOUT="$DUPER_TIMEOUT" \
  MAX_HEARTBEATS="$MAX_HEARTBEATS" MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
  CRUSH_PROFILE=true \
  RESUME="$resume" OUT_DIR="$dataset/plean" \
    bash "$ROOT/scripts/benchmark-plean.sh"
  reclaim_trees plean "$SMT_TREE_ROOT"
fi

if [[ "$skip_figures" == "true" ]]; then
  printf '\nMeasurement complete: %s\n' "$dataset"
  printf 'Draw the figures with --figures_only %s\n' "$dataset"
  exit 0
fi

draw_figures "$dataset"
[[ "$update_archive" == "true" ]] && pack_archive "$dataset"

printf '\nExperiments complete: %s\n' "$dataset"
