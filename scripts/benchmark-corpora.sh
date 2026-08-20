#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/benchmark-common.sh"

HAMMER_REPO="${HAMMER_REPO:-}"
LOOM_REPO="${LOOM_REPO:-}"
VELVET_REPO="${VELVET_REPO:-}"

HAMMER_REPO_URL="${HAMMER_REPO_URL:-https://github.com/AD1024/LeanHammer.git}"
LOOM_REPO_URL="${LOOM_REPO_URL:-https://github.com/AD1024/loom.git}"
VELVET_REPO_URL="${VELVET_REPO_URL:-https://github.com/AD1024/velvet.git}"
BENCHMARK_SOURCE_CACHE="${BENCHMARK_SOURCE_CACHE:-$CRUSH_ROOT/BenchmarkResults/sources}"

LOOM_AUTO_TREE="${LOOM_AUTO_TREE:-}"
LOOM_CRUSH_TREE="${LOOM_CRUSH_TREE:-}"
LOOM_DUPER_TREE="${LOOM_DUPER_TREE:-}"
VELVET_AUTO_TREE="${VELVET_AUTO_TREE:-}"
VELVET_CRUSH_TREE="${VELVET_CRUSH_TREE:-}"
VELVET_DUPER_TREE="${VELVET_DUPER_TREE:-}"

HAMMER_REF="${HAMMER_REF:-df4dd13671412591d678eada250b04c030fd4d40}"
LOOM_AUTO_REF="${LOOM_AUTO_REF:-78928abc9054b31d0bea85985496490baae95244}"
LOOM_CRUSH_REF="${LOOM_CRUSH_REF:-ec16b95ff8bbd047248de031cabd3160847e4b1b}"
LOOM_DUPER_REF="${LOOM_DUPER_REF:-616f9cd8db660dcd74a1c92b0d19bb50420e1c59}"
VELVET_AUTO_REF="${VELVET_AUTO_REF:-d254391d5e84546f96576e5b67dfb6bafe9fc301}"
VELVET_CRUSH_REF="${VELVET_CRUSH_REF:-e90d79341bb8ef510ec868623e74cfe98feaa4e8}"
VELVET_DUPER_REF="${VELVET_DUPER_REF:-5a1180338958908323a921255a8d158cf1f26c95}"

REPEATS="${REPEATS:-1}"
TIMEOUT="${TIMEOUT:-5}"
DUPER_TIMEOUT="${DUPER_TIMEOUT:-5}"
SOLVER="${SOLVER:-cvc5}"
CRUSH_MODES="${CRUSH_MODES:-verify core alethe portfolio}"
CRUSH_PROFILE="${CRUSH_PROFILE:-true}"
CRUSH_TRACE_INST="${CRUSH_TRACE_INST:-false}"
MAX_HEARTBEATS="${MAX_HEARTBEATS:-1000000}"
MAX_RECURSION_DEPTH="${MAX_RECURSION_DEPTH:-100000}"
GRIND_SPLITS="${GRIND_SPLITS:-20}"

RUN_AUTO="${RUN_AUTO:-true}"
RUN_CRUSH="${RUN_CRUSH:-true}"
RUN_DUPER="${RUN_DUPER:-true}"
RUN_GRIND="${RUN_GRIND:-true}"
RUN_LEANHAMMER="${RUN_LEANHAMMER:-true}"
RUN_LOOM="${RUN_LOOM:-true}"
RUN_CASHMERE="${RUN_CASHMERE:-true}"
RUN_VELVET="${RUN_VELVET:-true}"
USE_MATHLIB_CACHE="${USE_MATHLIB_CACHE:-true}"
KEEP_WORKTREES="${KEEP_WORKTREES:-false}"

CASHMERE_CASES="${CASHMERE_CASES:-}"
VELVET_CASES="${VELVET_CASES:-}"
OUT_DIR="${OUT_DIR:-$CRUSH_ROOT/BenchmarkResults/corpora-$(date +%Y%m%d-%H%M%S)}"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/lean-crush-corpora.XXXXXX")"

RESULTS="$OUT_DIR/results.tsv"
RUNS="$OUT_DIR/runs.tsv"
METADATA="$OUT_DIR/metadata.tsv"
SUMMARY="$OUT_DIR/summary.tsv"
MATCHED_SUMMARY="$OUT_DIR/matched-summary.tsv"
COMPARISON="$OUT_DIR/comparison.tsv"
MEASUREMENTS="$OUT_DIR/measurements.tsv"
PROFILES="$OUT_DIR/profile-events.tsv"

WORKTREES=()
ADDED_WORKTREE=""
TRUNCATED_RUNS=0

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

is_true() {
  [[ "$1" == "true" ]]
}

is_crush_lane() {
  [[ "$1" == crush-* ]]
}

crush_lane_trust() {
  case "$1" in
    crush-verify) printf 'trust\n' ;;
    crush-core|crush-alethe|crush-portfolio) printf 'reconstruct\n' ;;
    *) printf '%s\n' '-' ;;
  esac
}

crush_lane_reconstruct() {
  case "$1" in
    crush-core) printf 'core\n' ;;
    crush-alethe) printf 'alethe\n' ;;
    crush-verify|crush-portfolio) printf 'auto\n' ;;
    *) printf '%s\n' '-' ;;
  esac
}

CRUSH_LANES=()
if is_true "$RUN_CRUSH"; then
  for mode in $CRUSH_MODES; do
    case "$mode" in
      verify|core|alethe|portfolio)
        CRUSH_LANES+=("crush-$mode")
        ;;
      *)
        die "unknown Crush measurement mode: $mode"
        ;;
    esac
  done
fi

find_solver() {
  local name="$1"
  local configured="$2"
  local candidate
  if [[ -n "$configured" && -x "$configured" ]]; then
    printf '%s\n' "$configured"
    return
  fi
  candidate="$(command -v "$name" 2>/dev/null || true)"
  if [[ -n "$candidate" && -x "$candidate" ]]; then
    printf '%s\n' "$candidate"
    return
  fi
  for candidate in \
      "$LOOM_REPO/.lake/build/$name" \
      "$VELVET_REPO/.lake/packages/Loom/.lake/build/$name"; do
    if [[ -x "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return
    fi
  done
  return 1
}

Z3_BIN="$(find_solver z3 "${Z3_BIN:-}")" ||
  die "z3 not found; set Z3_BIN to an executable"
CVC5_BIN="$(find_solver cvc5 "${CVC5_BIN:-}")" ||
  die "cvc5 not found; set CVC5_BIN to an executable"

check_repo() {
  local repo="$1"
  local label="$2"
  benchmark_is_git_repo "$repo" ||
    die "$label repository not found at $repo"
}

check_ref() {
  local repo="$1"
  local ref="$2"
  git -C "$repo" rev-parse --verify "${ref}^{commit}" >/dev/null 2>&1 ||
    die "ref $ref is unavailable in $repo"
}

cleanup() {
  local entry repo path
  if is_true "$KEEP_WORKTREES"; then
    printf 'Temporary worktrees retained at %s\n' "$TMP_ROOT"
    return
  fi
  if [[ "${#WORKTREES[@]}" -gt 0 ]]; then
    for entry in "${WORKTREES[@]}"; do
      repo="${entry%%|*}"
      path="${entry#*|}"
      git -C "$repo" worktree remove --force "$path" >/dev/null 2>&1 || true
    done
  fi
  rm -rf "$TMP_ROOT"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

add_worktree() {
  local repo="$1"
  local ref="$2"
  local name="$3"
  local path="$TMP_ROOT/$name"
  benchmark_add_worktree "$repo" "$ref" "$path" >/dev/null ||
    die "failed to create worktree for $repo at $ref"
  WORKTREES+=("$repo|$path")
  ADDED_WORKTREE="$path"
}

seed_solvers() {
  local tree="$1"
  local dir
  for dir in "$tree/.lake/build" "$tree/.lake/packages/Loom/.lake/build"; do
    if [[ "$dir" == *"/packages/Loom/"* && ! -d "$tree/.lake/packages/Loom" ]]; then
      continue
    fi
    mkdir -p "$dir"
    if [[ ! -x "$dir/z3" ]]; then
      cp "$Z3_BIN" "$dir/z3"
    fi
    if [[ ! -x "$dir/cvc5" ]]; then
      cp "$CVC5_BIN" "$dir/cvc5"
    fi
    chmod +x "$dir/z3" "$dir/cvc5"
  done
}

sync_local_crush_sources() {
  local tree="$1"
  benchmark_sync_crush_sources "$CRUSH_ROOT" "$tree" ||
    die "failed to synchronize local Crush sources"
}

prepare_tree() {
  local label="$1"
  local tree="$2"
  shift 2
  printf 'Preparing %s\n' "$label"

  if ! (cd "$tree" && lake env printenv LEAN_PATH) \
      > "$OUT_DIR/dependencies-$label.log" 2>&1; then
    tail -n 80 "$OUT_DIR/dependencies-$label.log" >&2
    die "$label dependency setup failed"
  fi
  if is_true "$USE_MATHLIB_CACHE"; then
    if ! (cd "$tree" && lake exe cache get) > "$OUT_DIR/cache-$label.log" 2>&1; then
      printf 'warning: Mathlib cache unavailable for %s; building from source\n' "$label" >&2
    fi
  fi

  # Loom resolves solver paths relative to its own package. Seed both possible
  # locations after Lake has materialized dependencies so no download target runs.
  seed_solvers "$tree"
  if [[ "$label" == *"-crush" ]]; then
    sync_local_crush_sources "$tree"
  fi

  if ! (cd "$tree" && lake build "$@") > "$OUT_DIR/build-$label.log" 2>&1; then
    tail -n 80 "$OUT_DIR/build-$label.log" >&2
    die "$label build failed; see $OUT_DIR/build-$label.log"
  fi
}

record_metadata() {
  local suite="$1"
  local backend="$2"
  local ref="$3"
  local tree="$4"
  local commit toolchain crush_commit crush_dirty duper_commit trust reconstruct
  commit="$(git -C "$tree" rev-parse HEAD)"
  toolchain="$(tr -d '\r\n' < "$tree/lean-toolchain")"
  crush_commit="-"
  crush_dirty="false"
  duper_commit="-"
  if is_crush_lane "$backend"; then
    crush_commit="$(git -C "$CRUSH_ROOT" rev-parse HEAD)"
    if [[ -n "$(git -C "$CRUSH_ROOT" status --porcelain -- \
        . ':(exclude)BenchmarkResults')" ]]; then
      crush_dirty="true"
    fi
  fi
  if [[ "$backend" == "duper" ]]; then
    duper_commit="$(git -C "$tree/.lake/packages/Duper" rev-parse HEAD)"
  fi
  trust="$(crush_lane_trust "$backend")"
  reconstruct="$(crush_lane_reconstruct "$backend")"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$suite" "$backend" "$ref" "$commit" "$toolchain" "$SOLVER" "$TIMEOUT" \
    "$DUPER_TIMEOUT" "$MAX_HEARTBEATS" "$MAX_RECURSION_DEPTH" "$trust" \
    "$reconstruct" "$crush_commit" "$duper_commit" "$crush_dirty" "$tree" \
    "$CRUSH_PROFILE" \
    >> "$METADATA"
}

write_prelude() {
  local output="$1"
  local backend="$2"
  local trust reconstruct

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic|
    set_option loom.solver "$SOLVER" in
    set_option loom.solver.smt.timeout $TIMEOUT in
    loom_auto)
EOF
  elif is_crush_lane "$backend"; then
    trust="$(crush_lane_trust "$backend")"
    reconstruct="$(crush_lane_reconstruct "$backend")"
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic|
    set_option crush.backend "$SOLVER" in
    set_option crush.timeout $TIMEOUT in
    set_option crush.trust "$trust" in
    set_option crush.reconstruct "$reconstruct" in
    set_option crush.profile $CRUSH_PROFILE in
    set_option crush.profile.machine true in
    set_option trace.crush.inst $CRUSH_TRACE_INST in
    loom_crush)
EOF
  elif [[ "$backend" == "grind" ]]; then
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic| grind (splits := $GRIND_SPLITS))
EOF
  else
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic|
    set_option duper.maxSaturationTime $DUPER_TIMEOUT in
    loom_duper)
EOF
  fi

  cat >> "$output" <<EOF

private def corpusBenchMaxHeartbeats : Nat := $MAX_HEARTBEATS * 1000
EOF

  cat >> "$output" <<'EOF'

open Lean Elab Tactic Meta

private def corpusBenchContains (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

private def corpusBenchCategory (msg : String) : String :=
  if corpusBenchContains msg "timeout" || corpusBenchContains msg "heartbeat" then "timeout"
  else if corpusBenchContains msg "unknown" then "unknown"
  else if corpusBenchContains msg "not provable" ||
      corpusBenchContains msg "the goal is false" then "sat"
  else if corpusBenchContains msg "translation" ||
      corpusBenchContains msg "unsupported" then "translation"
  else if corpusBenchContains msg "reconstruction" ||
      corpusBenchContains msg "Alethe" then "reconstruction"
  else "tactic"

private def runCorpusBench : TacticM Unit := Lean.withCurrHeartbeats do
  withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := corpusBenchMaxHeartbeats }) do
    withMainContext do
      let goal <- getMainGoal
      let goalText := (toString (← ppExpr (← goal.getType)))
        |>.replace "\t" " "
        |>.replace "\n" " "
      let goalHash := hash goalText
      let proofName := (← Term.getDeclName?).getD `anonymous
      let vc := goalHash
      let saved <- saveState
      let start <- IO.monoMsNow
      try
        evalTactic (← `(tactic| corpus_backend))
        unless (← getUnsolvedGoals).isEmpty do
          throwError "backend returned without closing the goal"
        let elapsed := (← IO.monoMsNow) - start
        IO.println s!"CORPUS_BENCH\t{proofName}\t{vc}\t{goalHash}\tpass\t-\t{elapsed}\t-\t{goalText}"
      catch ex =>
        let elapsed := (← IO.monoMsNow) - start
        let msg := (← ex.toMessageData.toString)
          |>.replace "\t" " "
          |>.replace "\n" " "
        saved.restore
        IO.println s!"CORPUS_BENCH\t{proofName}\t{vc}\t{goalHash}\tfail\t{corpusBenchCategory msg}\t{elapsed}\t{msg}\t{goalText}"

syntax "corpus_bench_solver" : tactic

elab_rules : tactic
  | `(tactic| corpus_bench_solver) => runCorpusBench

macro_rules
  | `(tactic| loom_solver) => `(tactic| corpus_bench_solver)

EOF
}

write_benchmark_file() {
  local source="$1"
  local output="$2"
  local backend="$3"
  local last_import

  last_import="$(awk '/^import / { line = NR } END { print line + 0 }' "$source")"
  [[ "$last_import" -gt 0 ]] || die "no imports found in $source"
  head -n "$last_import" "$source" > "$output"
  write_prelude "$output" "$backend"

  tail -n "+$((last_import + 1))" "$source" |
    sed -E \
      -e 's/loom_solve_async!?([[:space:]]+[0-9]+)?/loom_solve/g' \
      -e 's/loom_solve[!?]/loom_solve/g' \
      -e 's/[[:space:]]*<;>[[:space:]]*try[[:space:]]+loom_crush//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*try[[:space:]]+loom_auto//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*try[[:space:]]+loom_duper//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_crush//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_auto//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_duper//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_smt[[:space:]]+\[\*\]//g' \
      -e 's/loom_crush/corpus_bench_solver/g' \
      -e 's/loom_auto/corpus_bench_solver/g' \
      -e 's/loom_duper/corpus_bench_solver/g' \
      -e 's/loom_smt[[:space:]]+\[[^]]*\]/corpus_bench_solver/g' \
      -e 's/^[[:space:]]*set_option[[:space:]]+maxHeartbeats[[:space:]]+[0-9]+[[:space:]]*$/set_option maxHeartbeats 0/' \
      >> "$output"
}

write_loom_fixture() {
  local output="$1"
  local backend="$2"
  printf 'import CaseStudies.Tactic\n' > "$output"
  write_prelude "$output" "$backend"
  cat >> "$output" <<'EOF'

example (balance amount oldBalance : Int)
    (h : balance + amount = oldBalance) :
    balance = oldBalance - amount := by
  corpus_bench_solver

example (arr : Nat -> Int) (i : Nat) (mx mx' : Int)
    (h : forall j, j < i -> arr j <= mx)
    (hmx' : mx' = if arr i >= mx then arr i else mx) :
    forall j, j < i + 1 -> arr j <= mx' := by
  corpus_bench_solver

example (arr arr' : Nat -> Int) (i : Nat) (key : Int)
    (hupd : forall k, arr' k = if k = i then key else arr k)
    (h : forall j, j < i -> arr j <= key) (hkey : arr i <= key) :
    forall j, j <= i -> arr' j <= key := by
  corpus_bench_solver

example (sum rest total : Int)
    (hinvariant : sum + rest = total) (hnonnegative : 0 <= sum) :
    sum + rest = total /\ 0 <= sum := by
  corpus_bench_solver
EOF
}

append_records() {
  local suite="$1"
  local backend="$2"
  local ref="$3"
  local commit="$4"
  local toolchain="$5"
  local repeat="$6"
  local file="$7"
  local log="$8"

  awk -v suite="$suite" -v backend="$backend" -v ref="$ref" \
      -v commit="$commit" -v toolchain="$toolchain" -v repeat="$repeat" \
      -v file="$file" -v measurements="$MEASUREMENTS" '
    BEGIN { FS = OFS = "\t" }
    {
      marker = index($0, "CORPUS_BENCH\t")
      if (marker == 0) next
      line = substr($0, marker)
      split(line, result, "\t")
      print suite, backend, ref, commit, toolchain, repeat, file,
            result[2], result[3], result[4], result[5], result[6],
            result[7], result[8], result[9]
      vcKey = file "|" result[2] "|" result[4]
      print suite, backend, repeat, vcKey, result[5], result[6],
            result[7], result[8] >> measurements
    }
  ' "$log" >> "$RESULTS"
}

append_profile_records() {
  local suite="$1"
  local backend="$2"
  local repeat="$3"
  local file="$4"
  local log="$5"

  awk -v suite="$suite" -v lane="$backend" -v repeat="$repeat" \
      -v file="$file" -v profiles="$PROFILES" '
    BEGIN { FS = OFS = "\t"; pending = 0 }
    {
      profileMarker = index($0, "CRUSH_PROFILE\t")
      if (profileMarker > 0) {
        line = substr($0, profileMarker)
        split(line, profile, "\t")
        pending++
        declaration[pending] = profile[3]
        profileHash[pending] = profile[4]
        outcome[pending] = profile[5]
        replay[pending] = profile[6]
        detail[pending] = profile[7]
        totalNanos[pending] = profile[8]
        phases[pending] = profile[9]
        metrics[pending] = profile[10]
        next
      }
      resultMarker = index($0, "CORPUS_BENCH\t")
      if (resultMarker == 0) next
      line = substr($0, resultMarker)
      split(line, result, "\t")
      vcKey = file "|" result[2] "|" result[4]
      for (i = 1; i <= pending; i++) {
        print suite, lane, repeat, vcKey, declaration[i], profileHash[i],
              outcome[i], replay[i], detail[i], totalNanos[i], phases[i],
              metrics[i] >> profiles
        delete declaration[i]
        delete profileHash[i]
        delete outcome[i]
        delete replay[i]
        delete detail[i]
        delete totalNanos[i]
        delete phases[i]
        delete metrics[i]
      }
      pending = 0
    }
  ' "$log"
}

run_lean_file() {
  local suite="$1"
  local backend="$2"
  local ref="$3"
  local tree="$4"
  local repeat="$5"
  local label="$6"
  local generated="$7"
  local log="$OUT_DIR/logs/$suite/$backend/${label//\//_}.$repeat.log"
  local started elapsed exit_code vc_count commit toolchain truncated message

  commit="$(git -C "$tree" rev-parse HEAD)"
  toolchain="$(tr -d '\r\n' < "$tree/lean-toolchain")"
  printf '%-9s %-5s run %s: %s\n' "$suite" "$backend" "$repeat" "$label"
  started="$(date +%s)"
  if is_crush_lane "$backend"; then
    "$CRUSH_ROOT/scripts/with-local-crush.sh" "$tree" \
      "-DmaxHeartbeats=0" "-DmaxRecDepth=$MAX_RECURSION_DEPTH" \
      "$generated" > "$log" 2>&1
  else
    (cd "$tree" && lake env lean "-DmaxHeartbeats=0" \
      "-DmaxRecDepth=$MAX_RECURSION_DEPTH" "$generated") \
      > "$log" 2>&1
  fi
  exit_code=$?
  elapsed="$(( $(date +%s) - started ))"
  truncated="false"
  message="-"
  if grep -qE 'error: .*maximum number of heartbeats' "$log"; then
    truncated="true"
    message="declaration heartbeat exhaustion"
    TRUNCATED_RUNS=$((TRUNCATED_RUNS + 1))
    printf 'warning: %s %s was truncated by its declaration heartbeat limit\n' \
      "$suite" "$label" >&2
  fi
  vc_count="$(awk '/CORPUS_BENCH\t/ { n++ } END { print n + 0 }' "$log")"
  append_records "$suite" "$backend" "$ref" "$commit" "$toolchain" \
    "$repeat" "$label" "$log"
  append_profile_records "$suite" "$backend" "$repeat" "$label" "$log"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$suite" "$backend" "$repeat" "$label" "$exit_code" "$elapsed" "$vc_count" \
    "$truncated" "$message" \
    >> "$RUNS"
}

run_fixture() {
  local backend="$1"
  local ref="$2"
  local tree="$3"
  local repeat generated
  mkdir -p "$TMP_ROOT/generated/loom/$backend" "$OUT_DIR/logs/loom/$backend"
  generated="$TMP_ROOT/generated/loom/$backend/LoomBackend.lean"
  write_loom_fixture "$generated" "$backend"
  for repeat in $(seq 1 "$REPEATS"); do
    run_lean_file "loom" "$backend" "$ref" "$tree" "$repeat" \
      "LoomBackend.lean" "$generated"
  done
}

run_files() {
  local suite="$1"
  local backend="$2"
  local ref="$3"
  local tree="$4"
  shift 4
  local files=("$@")
  local repeat file source generated

  mkdir -p "$TMP_ROOT/generated/$suite/$backend" "$OUT_DIR/logs/$suite/$backend"
  for repeat in $(seq 1 "$REPEATS"); do
    for file in "${files[@]}"; do
      source="$tree/$file"
      if [[ ! -f "$source" ]]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
          "$suite" "$backend" "$repeat" "$file" "missing" "0" "0" "source file missing" \
          >> "$RUNS"
        continue
      fi
      generated="$TMP_ROOT/generated/$suite/$backend/${file//\//_}"
      write_benchmark_file "$source" "$generated" "$backend"
      run_lean_file "$suite" "$backend" "$ref" "$tree" "$repeat" "$file" "$generated"
    done
  done
}

write_reports() {
  awk -F '\t' '
    BEGIN {
      OFS = "\t"
      print "suite", "backend", "attempted", "passed", "failed", "pass_pct",
            "total_ms", "mean_ms", "min_ms", "max_ms", "successful_mean_ms"
    }
    NR > 1 {
      key = $1 SUBSEP $2
      seen[key] = 1
      attempted[key]++
      total[key] += $13
      if (!(key in minimum) || $13 < minimum[key]) minimum[key] = $13
      if (!(key in maximum) || $13 > maximum[key]) maximum[key] = $13
      if ($11 == "pass") {
        passed[key]++
        elapsed[key] += $13
      }
    }
    END {
      for (key in seen) {
        split(key, p, SUBSEP)
        failed = attempted[key] - passed[key]
        pct = attempted[key] ? 100 * passed[key] / attempted[key] : 0
        successfulMean = passed[key] ? elapsed[key] / passed[key] : 0
        printf "%s\t%s\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\n",
          p[1], p[2], attempted[key], passed[key], failed, pct,
          total[key], attempted[key] ? total[key] / attempted[key] : 0,
          minimum[key], maximum[key], successfulMean
      }
    }
  ' "$RESULTS" > "$SUMMARY"

  awk -F '\t' -v repeats="$REPEATS" '
    BEGIN {
      OFS = "\t"
      backend[1] = "auto"
      backend[2] = "duper"
      backend[3] = "crush-portfolio"
      print "suite", "backend", "attempted", "passed", "failed", "pass_pct",
            "total_ms", "mean_ms", "min_ms", "max_ms"
    }
    NR > 1 {
      vc = $1 SUBSEP $7 SUBSEP $8 SUBSEP $9 SUBSEP $10
      run = vc SUBSEP $2 SUBSEP $6
      runSeen[run] = 1
      runMs[run] += $13
      if ($11 != "pass") runFailed[run] = 1
    }
    END {
      for (run in runSeen) {
        split(run, p, SUBSEP)
        vc = p[1] SUBSEP p[2] SUBSEP p[3] SUBSEP p[4] SUBSEP p[5]
        key = vc SUBSEP p[6]
        runs[key]++
        totalMs[key] += runMs[run]
        if (!runFailed[run]) passRuns[key]++
        vcs[vc] = 1
      }
      for (vc in vcs) {
        autoKey = vc SUBSEP "auto"
        duperKey = vc SUBSEP "duper"
        crushKey = vc SUBSEP "crush-portfolio"
        if (runs[autoKey] != repeats || runs[duperKey] != repeats ||
            runs[crushKey] != repeats) continue
        split(vc, p, SUBSEP)
        suite = p[1]
        for (i = 1; i <= 3; i++) {
          name = backend[i]
          sourceKey = vc SUBSEP name
          resultKey = suite SUBSEP name
          elapsed = totalMs[sourceKey] / repeats
          attempted[resultKey]++
          total[resultKey] += elapsed
          if (!(resultKey in minimum) || elapsed < minimum[resultKey])
            minimum[resultKey] = elapsed
          if (!(resultKey in maximum) || elapsed > maximum[resultKey])
            maximum[resultKey] = elapsed
          if (passRuns[sourceKey] == repeats) passed[resultKey]++
        }
      }
      for (resultKey in attempted) {
        split(resultKey, p, SUBSEP)
        failed = attempted[resultKey] - passed[resultKey]
        pct = 100 * passed[resultKey] / attempted[resultKey]
        printf "%s\t%s\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\n",
          p[1], p[2], attempted[resultKey], passed[resultKey], failed, pct,
          total[resultKey], total[resultKey] / attempted[resultKey],
          minimum[resultKey], maximum[resultKey]
      }
    }
  ' "$RESULTS" > "$MATCHED_SUMMARY"

  awk -F '\t' -v repeats="$REPEATS" '
    BEGIN {
      OFS = "\t"
      left[1] = "auto";  right[1] = "crush-portfolio"
      left[2] = "auto";  right[2] = "duper"
      left[3] = "duper"; right[3] = "crush-portfolio"
      left[4] = "grind"; right[4] = "crush-portfolio"
      left[5] = "auto";  right[5] = "grind"
      left[6] = "duper"; right[6] = "grind"
      print "suite", "left_backend", "right_backend", "shared_vcs",
            "left_only", "right_only", "both_solved", "neither_solved",
            "left_mean_ms", "right_mean_ms"
    }
    NR > 1 {
      vc = $1 SUBSEP $7 SUBSEP $8 SUBSEP $9 SUBSEP $10
      run = vc SUBSEP $2 SUBSEP $6
      runSeen[run] = 1
      runMs[run] += $13
      if ($11 != "pass") runFailed[run] = 1
      suites[$1] = 1
    }
    END {
      for (run in runSeen) {
        split(run, p, SUBSEP)
        vc = p[1] SUBSEP p[2] SUBSEP p[3] SUBSEP p[4] SUBSEP p[5]
        backend = p[6]
        key = vc SUBSEP backend
        runs[key]++
        totalMs[key] += runMs[run]
        if (!runFailed[run]) passRuns[key]++
        vcs[vc] = 1
      }
      for (vc in vcs) {
        split(vc, p, SUBSEP)
        suite = p[1]
        for (pair = 1; pair <= 6; pair++) {
          leftKey = vc SUBSEP left[pair]
          rightKey = vc SUBSEP right[pair]
          if (runs[leftKey] != repeats || runs[rightKey] != repeats) continue
          resultKey = suite SUBSEP pair
          shared[resultKey]++
          leftSolved = passRuns[leftKey] == repeats
          rightSolved = passRuns[rightKey] == repeats
          if (leftSolved && !rightSolved) leftOnly[resultKey]++
          if (!leftSolved && rightSolved) rightOnly[resultKey]++
          if (!leftSolved && !rightSolved) neither[resultKey]++
          if (leftSolved && rightSolved) {
            both[resultKey]++
            leftMs[resultKey] += totalMs[leftKey] / repeats
            rightMs[resultKey] += totalMs[rightKey] / repeats
          }
        }
      }
      for (suite in suites) {
        for (pair = 1; pair <= 6; pair++) {
          resultKey = suite SUBSEP pair
          if (!shared[resultKey]) continue
          leftMean = both[resultKey] ? leftMs[resultKey] / both[resultKey] : 0
          rightMean = both[resultKey] ? rightMs[resultKey] / both[resultKey] : 0
          printf "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%.1f\t%.1f\n",
            suite, left[pair], right[pair], shared[resultKey],
            leftOnly[resultKey], rightOnly[resultKey], both[resultKey],
            neither[resultKey], leftMean, rightMean
        }
      }
    }
  ' "$RESULTS" > "$COMPARISON"
}

check_repo "$CRUSH_ROOT" "lean-crush"
if ! is_true "$RUN_AUTO" && ! is_true "$RUN_CRUSH" && ! is_true "$RUN_DUPER" &&
    ! is_true "$RUN_GRIND"; then
  die "at least one backend must be enabled"
fi

mkdir -p "$OUT_DIR/logs"
printf 'Building local Crush\n'
if ! (cd "$CRUSH_ROOT" && lake build Crush) \
    > "$OUT_DIR/build-crush.log" 2>&1; then
  tail -n 80 "$OUT_DIR/build-crush.log" >&2
  die "local Crush build failed"
fi

if is_true "$RUN_LEANHAMMER"; then
  if [[ -z "$HAMMER_REPO" ]]; then
    hammer_source="$(benchmark_ensure_repo "LeanHammer" "$HAMMER_REPO_URL" \
      "$HAMMER_REF" "$BENCHMARK_SOURCE_CACHE/LeanHammer")" ||
      die "failed to provision LeanHammer"
    add_worktree "$hammer_source" "$HAMMER_REF" "leanhammer"
    HAMMER_REPO="$ADDED_WORKTREE"
  else
    HAMMER_REPO="$(cd "$HAMMER_REPO" && pwd)"
  fi
  check_repo "$HAMMER_REPO" "LeanHammer"
fi
if is_true "$RUN_LOOM" || is_true "$RUN_CASHMERE"; then
  loom_need_auto=false
  loom_need_crush=false
  loom_need_duper=false
  if is_true "$RUN_AUTO" && [[ -z "$LOOM_AUTO_TREE" ]]; then
    loom_need_auto=true
  fi
  if (is_true "$RUN_CRUSH" || is_true "$RUN_GRIND") &&
      [[ -z "$LOOM_CRUSH_TREE" ]]; then
    loom_need_crush=true
  fi
  if is_true "$RUN_DUPER" && [[ -z "$LOOM_DUPER_TREE" ]]; then
    loom_need_duper=true
  fi
  if is_true "$loom_need_auto" || is_true "$loom_need_crush" ||
      is_true "$loom_need_duper"; then
    loom_managed=false
    if [[ -z "$LOOM_REPO" ]]; then
      loom_managed=true
      if is_true "$loom_need_auto"; then
        LOOM_REPO="$(benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" \
          "$LOOM_AUTO_REF" "$BENCHMARK_SOURCE_CACHE/loom")" ||
          die "failed to provision Loom"
      elif is_true "$loom_need_crush"; then
        LOOM_REPO="$(benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" \
          "$LOOM_CRUSH_REF" "$BENCHMARK_SOURCE_CACHE/loom")" ||
          die "failed to provision Loom"
      else
        LOOM_REPO="$(benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" \
          "$LOOM_DUPER_REF" "$BENCHMARK_SOURCE_CACHE/loom")" ||
          die "failed to provision Loom"
      fi
    else
      LOOM_REPO="$(cd "$LOOM_REPO" && pwd)"
    fi
    check_repo "$LOOM_REPO" "Loom"
    if is_true "$loom_need_auto"; then
      if is_true "$loom_managed"; then
        benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" "$LOOM_AUTO_REF" \
          "$LOOM_REPO" >/dev/null ||
          die "failed to provision Loom auto revision"
      else
        check_ref "$LOOM_REPO" "$LOOM_AUTO_REF"
      fi
    fi
    if is_true "$loom_need_crush"; then
      if is_true "$loom_managed"; then
        benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" "$LOOM_CRUSH_REF" \
          "$LOOM_REPO" >/dev/null ||
          die "failed to provision Loom Crush revision"
      else
        check_ref "$LOOM_REPO" "$LOOM_CRUSH_REF"
      fi
    fi
    if is_true "$loom_need_duper"; then
      if is_true "$loom_managed"; then
        benchmark_ensure_repo "Loom" "$LOOM_REPO_URL" "$LOOM_DUPER_REF" \
          "$LOOM_REPO" >/dev/null ||
          die "failed to provision Loom Duper revision"
      else
        check_ref "$LOOM_REPO" "$LOOM_DUPER_REF"
      fi
    fi
  fi
fi
if is_true "$RUN_VELVET"; then
  velvet_need_auto=false
  velvet_need_crush=false
  velvet_need_duper=false
  if is_true "$RUN_AUTO" && [[ -z "$VELVET_AUTO_TREE" ]]; then
    velvet_need_auto=true
  fi
  if (is_true "$RUN_CRUSH" || is_true "$RUN_GRIND") &&
      [[ -z "$VELVET_CRUSH_TREE" ]]; then
    velvet_need_crush=true
  fi
  if is_true "$RUN_DUPER" && [[ -z "$VELVET_DUPER_TREE" ]]; then
    velvet_need_duper=true
  fi
  if is_true "$velvet_need_auto" || is_true "$velvet_need_crush" ||
      is_true "$velvet_need_duper"; then
    velvet_managed=false
    if [[ -z "$VELVET_REPO" ]]; then
      velvet_managed=true
      if is_true "$velvet_need_auto"; then
        VELVET_REPO="$(benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_AUTO_REF" "$BENCHMARK_SOURCE_CACHE/velvet")" ||
          die "failed to provision Velvet"
      elif is_true "$velvet_need_crush"; then
        VELVET_REPO="$(benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_CRUSH_REF" "$BENCHMARK_SOURCE_CACHE/velvet")" ||
          die "failed to provision Velvet"
      else
        VELVET_REPO="$(benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_DUPER_REF" "$BENCHMARK_SOURCE_CACHE/velvet")" ||
          die "failed to provision Velvet"
      fi
    else
      VELVET_REPO="$(cd "$VELVET_REPO" && pwd)"
    fi
    check_repo "$VELVET_REPO" "Velvet"
    if is_true "$velvet_need_auto"; then
      if is_true "$velvet_managed"; then
        benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_AUTO_REF" "$VELVET_REPO" >/dev/null ||
          die "failed to provision Velvet auto revision"
      else
        check_ref "$VELVET_REPO" "$VELVET_AUTO_REF"
      fi
    fi
    if is_true "$velvet_need_crush"; then
      if is_true "$velvet_managed"; then
        benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_CRUSH_REF" "$VELVET_REPO" >/dev/null ||
          die "failed to provision Velvet Crush revision"
      else
        check_ref "$VELVET_REPO" "$VELVET_CRUSH_REF"
      fi
    fi
    if is_true "$velvet_need_duper"; then
      if is_true "$velvet_managed"; then
        benchmark_ensure_repo "Velvet" "$VELVET_REPO_URL" \
          "$VELVET_DUPER_REF" "$VELVET_REPO" >/dev/null ||
          die "failed to provision Velvet Duper revision"
      else
        check_ref "$VELVET_REPO" "$VELVET_DUPER_REF"
      fi
    fi
  fi
fi

printf 'suite\tbackend\tref\tcommit\ttoolchain\trepeat\tfile\tproof\tvc\tgoal_hash\tstatus\tcategory\tmilliseconds\tmessage\tgoal\n' > "$RESULTS"
printf 'suite\tbackend\trepeat\tfile\texit_code\twall_seconds\tvc_count\ttruncated\tmessage\n' > "$RUNS"
printf 'suite\tbackend\tref\tcommit\ttoolchain\tsolver\ttimeout\tduper_timeout\tvc_max_heartbeats\tmax_rec_depth\tcrush_trust\tcrush_reconstruct\tcrush_commit\tduper_commit\tcrush_dirty\tworktree\tcrush_profile\n' > "$METADATA"
printf 'suite\tlane\trepeat\tvc_key\tstatus\tcategory\tmilliseconds\tmessage\n' > "$MEASUREMENTS"
printf 'suite\tlane\trepeat\tvc_key\tdeclaration\tgoal_hash\toutcome\treplay\tdetail\ttotal_nanos\tphases\tmetrics\n' > "$PROFILES"

if is_true "$RUN_LEANHAMMER"; then
  printf 'Running LeanHammer focused suite\n'
  hammer_out="$OUT_DIR/leanhammer"
  if HAMMER_REPO="$HAMMER_REPO" REPEATS="$REPEATS" OUT_DIR="$hammer_out" \
      MAX_RECURSION_DEPTH="$MAX_RECURSION_DEPTH" \
      "$CRUSH_ROOT/scripts/benchmark-leanhammer.sh" \
      > "$OUT_DIR/leanhammer.log" 2>&1; then
    tail -n 12 "$OUT_DIR/leanhammer.log"
  else
    tail -n 80 "$OUT_DIR/leanhammer.log" >&2
    die "LeanHammer benchmark failed"
  fi
fi

CASHMERE_FILES=(
  "CaseStudies/Cashmere/Cashmere.lean"
  "CaseStudies/Cashmere/CashmereIncorrectnessLogic.lean"
)

VELVET_FILES=(
  "Velvet/Examples/EncodeDecodeStr.lean"
  "Velvet/Examples/Examples.lean"
  "Velvet/Examples/Examples_Total.lean"
  "Velvet/Examples/GCD.lean"
  "Velvet/Examples/IsNonPrime.lean"
  "Velvet/Examples/IsSorted.lean"
  "Velvet/Examples/MaxElem.lean"
  "Velvet/Examples/MemAlloc.lean"
  "Velvet/Examples/Recursion.lean"
  "Velvet/Examples/SmallHeartBeats.lean"
  "Velvet/Examples/SpMSpV_Example.lean"
  "Velvet/Examples/SubstringSearch.lean"
  "Velvet/Examples/SumOfDigits.lean"
  "Velvet/Examples/TestLoopControl.lean"
  "Velvet/Examples/TestMatch.lean"
  "Velvet/Examples/Total_Partial_example.lean"
)

if [[ -n "$CASHMERE_CASES" ]]; then
  read -r -a CASHMERE_FILES <<< "$CASHMERE_CASES"
fi
if [[ -n "$VELVET_CASES" ]]; then
  read -r -a VELVET_FILES <<< "$VELVET_CASES"
fi

if is_true "$RUN_LOOM" || is_true "$RUN_CASHMERE"; then
  if is_true "$RUN_AUTO"; then
    if [[ -n "$LOOM_AUTO_TREE" ]]; then
      loom_auto_tree="$(cd "$LOOM_AUTO_TREE" && pwd)"
    else
      add_worktree "$LOOM_REPO" "$LOOM_AUTO_REF" "loom-auto"
      loom_auto_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$loom_auto_tree" rev-parse HEAD)" == \
        "$(git -C "$loom_auto_tree" rev-parse "${LOOM_AUTO_REF}^{commit}")" ]] ||
      die "LOOM_AUTO_TREE is not at $LOOM_AUTO_REF"
    prepare_tree "loom-auto" "$loom_auto_tree" \
      CaseStudies.Tactic CaseStudies.Cashmere.Syntax_Cashmere
  fi
  if is_true "$RUN_CRUSH" || is_true "$RUN_GRIND"; then
    if [[ -n "$LOOM_CRUSH_TREE" ]]; then
      loom_crush_tree="$(cd "$LOOM_CRUSH_TREE" && pwd)"
    else
      add_worktree "$LOOM_REPO" "$LOOM_CRUSH_REF" "loom-crush"
      loom_crush_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$loom_crush_tree" rev-parse HEAD)" == \
        "$(git -C "$loom_crush_tree" rev-parse "${LOOM_CRUSH_REF}^{commit}")" ]] ||
      die "LOOM_CRUSH_TREE is not at $LOOM_CRUSH_REF"
    prepare_tree "loom-crush" "$loom_crush_tree" \
      CaseStudies.Tactic CaseStudies.Cashmere.Syntax_Cashmere
  fi
  if is_true "$RUN_DUPER"; then
    if [[ -n "$LOOM_DUPER_TREE" ]]; then
      loom_duper_tree="$(cd "$LOOM_DUPER_TREE" && pwd)"
    else
      add_worktree "$LOOM_REPO" "$LOOM_DUPER_REF" "loom-duper"
      loom_duper_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$loom_duper_tree" rev-parse HEAD)" == \
        "$(git -C "$loom_duper_tree" rev-parse "${LOOM_DUPER_REF}^{commit}")" ]] ||
      die "LOOM_DUPER_TREE is not at $LOOM_DUPER_REF"
    prepare_tree "loom-duper" "$loom_duper_tree" \
      CaseStudies.Tactic CaseStudies.Cashmere.Syntax_Cashmere
  fi
fi

if is_true "$RUN_LOOM"; then
  if is_true "$RUN_AUTO"; then
    record_metadata "loom" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
    run_fixture "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
  fi
  if is_true "$RUN_CRUSH"; then
    for lane in "${CRUSH_LANES[@]}"; do
      record_metadata "loom" "$lane" "$LOOM_CRUSH_REF" "$loom_crush_tree"
      run_fixture "$lane" "$LOOM_CRUSH_REF" "$loom_crush_tree"
    done
  fi
  if is_true "$RUN_GRIND"; then
    record_metadata "loom" "grind" "$LOOM_CRUSH_REF" "$loom_crush_tree"
    run_fixture "grind" "$LOOM_CRUSH_REF" "$loom_crush_tree"
  fi
  if is_true "$RUN_DUPER"; then
    record_metadata "loom" "duper" "$LOOM_DUPER_REF" "$loom_duper_tree"
    run_fixture "duper" "$LOOM_DUPER_REF" "$loom_duper_tree"
  fi
fi

if is_true "$RUN_CASHMERE"; then
  if is_true "$RUN_AUTO"; then
    record_metadata "cashmere" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
    run_files "cashmere" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree" "${CASHMERE_FILES[@]}"
  fi
  if is_true "$RUN_CRUSH"; then
    for lane in "${CRUSH_LANES[@]}"; do
      record_metadata "cashmere" "$lane" "$LOOM_CRUSH_REF" "$loom_crush_tree"
      run_files "cashmere" "$lane" "$LOOM_CRUSH_REF" "$loom_crush_tree" "${CASHMERE_FILES[@]}"
    done
  fi
  if is_true "$RUN_GRIND"; then
    record_metadata "cashmere" "grind" "$LOOM_CRUSH_REF" "$loom_crush_tree"
    run_files "cashmere" "grind" "$LOOM_CRUSH_REF" "$loom_crush_tree" "${CASHMERE_FILES[@]}"
  fi
  if is_true "$RUN_DUPER"; then
    record_metadata "cashmere" "duper" "$LOOM_DUPER_REF" "$loom_duper_tree"
    run_files "cashmere" "duper" "$LOOM_DUPER_REF" "$loom_duper_tree" "${CASHMERE_FILES[@]}"
  fi
fi

if is_true "$RUN_VELVET"; then
  if is_true "$RUN_AUTO"; then
    if [[ -n "$VELVET_AUTO_TREE" ]]; then
      velvet_auto_tree="$(cd "$VELVET_AUTO_TREE" && pwd)"
    else
      add_worktree "$VELVET_REPO" "$VELVET_AUTO_REF" "velvet-auto"
      velvet_auto_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$velvet_auto_tree" rev-parse HEAD)" == \
        "$(git -C "$velvet_auto_tree" rev-parse "${VELVET_AUTO_REF}^{commit}")" ]] ||
      die "VELVET_AUTO_TREE is not at $VELVET_AUTO_REF"
    prepare_tree "velvet-auto" "$velvet_auto_tree" Velvet.Std
  fi
  if is_true "$RUN_CRUSH" || is_true "$RUN_GRIND"; then
    if [[ -n "$VELVET_CRUSH_TREE" ]]; then
      velvet_crush_tree="$(cd "$VELVET_CRUSH_TREE" && pwd)"
    else
      add_worktree "$VELVET_REPO" "$VELVET_CRUSH_REF" "velvet-crush"
      velvet_crush_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$velvet_crush_tree" rev-parse HEAD)" == \
        "$(git -C "$velvet_crush_tree" rev-parse "${VELVET_CRUSH_REF}^{commit}")" ]] ||
      die "VELVET_CRUSH_TREE is not at $VELVET_CRUSH_REF"
    prepare_tree "velvet-crush" "$velvet_crush_tree" Velvet.Std
  fi
  if is_true "$RUN_DUPER"; then
    if [[ -n "$VELVET_DUPER_TREE" ]]; then
      velvet_duper_tree="$(cd "$VELVET_DUPER_TREE" && pwd)"
    else
      add_worktree "$VELVET_REPO" "$VELVET_DUPER_REF" "velvet-duper"
      velvet_duper_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$velvet_duper_tree" rev-parse HEAD)" == \
        "$(git -C "$velvet_duper_tree" rev-parse "${VELVET_DUPER_REF}^{commit}")" ]] ||
      die "VELVET_DUPER_TREE is not at $VELVET_DUPER_REF"
    prepare_tree "velvet-duper" "$velvet_duper_tree" Velvet.Std
  fi
  if is_true "$RUN_AUTO"; then
    record_metadata "velvet" "auto" "$VELVET_AUTO_REF" "$velvet_auto_tree"
    run_files "velvet" "auto" "$VELVET_AUTO_REF" "$velvet_auto_tree" "${VELVET_FILES[@]}"
  fi
  if is_true "$RUN_CRUSH"; then
    for lane in "${CRUSH_LANES[@]}"; do
      record_metadata "velvet" "$lane" "$VELVET_CRUSH_REF" "$velvet_crush_tree"
      run_files "velvet" "$lane" "$VELVET_CRUSH_REF" "$velvet_crush_tree" "${VELVET_FILES[@]}"
    done
  fi
  if is_true "$RUN_GRIND"; then
    record_metadata "velvet" "grind" "$VELVET_CRUSH_REF" "$velvet_crush_tree"
    run_files "velvet" "grind" "$VELVET_CRUSH_REF" "$velvet_crush_tree" "${VELVET_FILES[@]}"
  fi
  if is_true "$RUN_DUPER"; then
    record_metadata "velvet" "duper" "$VELVET_DUPER_REF" "$velvet_duper_tree"
    run_files "velvet" "duper" "$VELVET_DUPER_REF" "$velvet_duper_tree" "${VELVET_FILES[@]}"
  fi
fi

write_reports
if ! python3 "$SCRIPT_DIR/benchmark-report.py" \
    --measurements "$MEASUREMENTS" --profiles "$PROFILES" --out-dir "$OUT_DIR"; then
  die "failed to generate measurement reports"
fi

printf '\nCorpus summary:\n'
column -t -s $'\t' "$SUMMARY" 2>/dev/null || cat "$SUMMARY"
printf '\nThree-way matched summary:\n'
column -t -s $'\t' "$MATCHED_SUMMARY" 2>/dev/null || cat "$MATCHED_SUMMARY"
printf '\nMatched-VC comparison:\n'
column -t -s $'\t' "$COMPARISON" 2>/dev/null || cat "$COMPARISON"
printf '\nReconstruction coverage:\n'
column -t -s $'\t' "$OUT_DIR/reconstruction-summary.tsv" 2>/dev/null ||
  cat "$OUT_DIR/reconstruction-summary.tsv"
printf '\nReconstruction failures:\n'
column -t -s $'\t' "$OUT_DIR/reconstruction-failures.tsv" 2>/dev/null ||
  cat "$OUT_DIR/reconstruction-failures.tsv"
printf '\nAlethe replay scaling:\n'
column -t -s $'\t' "$OUT_DIR/alethe-replay-scaling-summary.tsv" 2>/dev/null ||
  cat "$OUT_DIR/alethe-replay-scaling-summary.tsv"
printf '\nResults: %s\n' "$OUT_DIR"

if [[ "$TRUNCATED_RUNS" -gt 0 ]]; then
  die "$TRUNCATED_RUNS benchmark run(s) were truncated before all VCs were emitted"
fi
