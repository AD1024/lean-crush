#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PARENT="$(dirname "$CRUSH_ROOT")"

HAMMER_REPO="${HAMMER_REPO:-$PARENT/LeanHammer}"
LOOM_REPO="${LOOM_REPO:-$PARENT/loom}"
VELVET_REPO="${VELVET_REPO:-$PARENT/velvet}"

LOOM_AUTO_TREE="${LOOM_AUTO_TREE:-}"
LOOM_CRUSH_TREE="${LOOM_CRUSH_TREE:-}"
VELVET_AUTO_TREE="${VELVET_AUTO_TREE:-}"
VELVET_CRUSH_TREE="${VELVET_CRUSH_TREE:-}"

LOOM_AUTO_REF="${LOOM_AUTO_REF:-origin/master}"
LOOM_CRUSH_REF="${LOOM_CRUSH_REF:-origin/crush-backend}"
VELVET_AUTO_REF="${VELVET_AUTO_REF:-origin/master}"
VELVET_CRUSH_REF="${VELVET_CRUSH_REF:-origin/crush-backend}"

REPEATS="${REPEATS:-1}"
TIMEOUT="${TIMEOUT:-5}"
SOLVER="${SOLVER:-cvc5}"
CRUSH_TRUST="${CRUSH_TRUST:-reconstruct}"
CRUSH_PROFILE="${CRUSH_PROFILE:-false}"
CRUSH_TRACE_INST="${CRUSH_TRACE_INST:-false}"
MAX_HEARTBEATS="${MAX_HEARTBEATS:-1000000}"

RUN_AUTO="${RUN_AUTO:-true}"
RUN_CRUSH="${RUN_CRUSH:-true}"
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
COMPARISON="$OUT_DIR/comparison.tsv"

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
  [[ -d "$repo/.git" ]] || die "$label repository not found at $repo"
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
  rmdir "$TMP_ROOT" >/dev/null 2>&1 || true
}
trap cleanup EXIT INT TERM

add_worktree() {
  local repo="$1"
  local ref="$2"
  local name="$3"
  local path="$TMP_ROOT/$name"
  git -C "$repo" worktree add --detach "$path" "$ref" >/dev/null ||
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
  local package="$tree/.lake/packages/crush"
  [[ -d "$package/Crush" ]] ||
    die "lean-crush dependency not materialized at $package"
  # The benchmark executes with the local Crush olean first on LEAN_PATH. Mirror
  # its sources into Lake's dependency checkout before building downstream modules
  # so structure/API changes cannot leave those modules ABI-stale.
  rsync -a --delete "$CRUSH_ROOT/Crush/" "$package/Crush/"
  cp "$CRUSH_ROOT/Crush.lean" "$package/Crush.lean"
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
  local commit toolchain crush_commit crush_dirty
  commit="$(git -C "$tree" rev-parse HEAD)"
  toolchain="$(tr -d '\r\n' < "$tree/lean-toolchain")"
  crush_commit="-"
  crush_dirty="false"
  if [[ "$backend" == "crush" ]]; then
    crush_commit="$(git -C "$CRUSH_ROOT" rev-parse HEAD)"
    if [[ -n "$(git -C "$CRUSH_ROOT" status --porcelain -- \
        . ':(exclude)BenchmarkResults')" ]]; then
      crush_dirty="true"
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$suite" "$backend" "$ref" "$commit" "$toolchain" "$SOLVER" "$TIMEOUT" \
    "$MAX_HEARTBEATS" "$CRUSH_TRUST" "$crush_commit" "$crush_dirty" "$tree" \
    >> "$METADATA"
}

write_prelude() {
  local output="$1"
  local backend="$2"

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic|
    set_option loom.solver "$SOLVER" in
    set_option loom.solver.smt.timeout $TIMEOUT in
    loom_auto)
EOF
  else
    cat >> "$output" <<EOF

macro "corpus_backend" : tactic =>
  \`(tactic|
    set_option crush.backend "$SOLVER" in
    set_option crush.timeout $TIMEOUT in
    set_option crush.trust "$CRUSH_TRUST" in
    set_option crush.profile $CRUSH_PROFILE in
    set_option trace.crush.inst $CRUSH_TRACE_INST in
    loom_crush)
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
  else if corpusBenchContains msg "reconstruction" then "reconstruction"
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
      -e 's/[[:space:]]*<;>[[:space:]]*loom_crush//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_auto//g' \
      -e 's/[[:space:]]*<;>[[:space:]]*loom_smt[[:space:]]+\[\*\]//g' \
      -e 's/loom_crush/corpus_bench_solver/g' \
      -e 's/loom_auto/corpus_bench_solver/g' \
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
      -v file="$file" '
    BEGIN { FS = OFS = "\t" }
    {
      marker = index($0, "CORPUS_BENCH\t")
      if (marker == 0) next
      line = substr($0, marker)
      split(line, result, "\t")
      print suite, backend, ref, commit, toolchain, repeat, file,
            result[2], result[3], result[4], result[5], result[6],
            result[7], result[8], result[9]
    }
  ' "$log" >> "$RESULTS"
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
  if [[ "$backend" == "crush" ]]; then
    "$CRUSH_ROOT/scripts/with-local-crush.sh" "$tree" \
      "-DmaxHeartbeats=0" "$generated" > "$log" 2>&1
  else
    (cd "$tree" && lake env lean "-DmaxHeartbeats=0" "$generated") \
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
      print "suite", "shared_vcs", "auto_only_wins", "crush_only_wins",
            "both_solved", "neither_solved", "auto_mean_ms", "crush_mean_ms"
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
        autoKey = vc SUBSEP "auto"
        crushKey = vc SUBSEP "crush"
        if (runs[autoKey] != repeats || runs[crushKey] != repeats) continue
        shared[suite]++
        autoSolved = passRuns[autoKey] == repeats
        crushSolved = passRuns[crushKey] == repeats
        if (autoSolved && !crushSolved) autoWins[suite]++
        if (!autoSolved && crushSolved) crushWins[suite]++
        if (!autoSolved && !crushSolved) neither[suite]++
        if (autoSolved && crushSolved) {
          both[suite]++
          autoMs[suite] += totalMs[autoKey] / repeats
          crushMs[suite] += totalMs[crushKey] / repeats
        }
      }
      for (suite in suites) {
        autoMean = both[suite] ? autoMs[suite] / both[suite] : 0
        crushMean = both[suite] ? crushMs[suite] / both[suite] : 0
        printf "%s\t%d\t%d\t%d\t%d\t%d\t%.1f\t%.1f\n",
          suite, shared[suite], autoWins[suite], crushWins[suite],
          both[suite], neither[suite], autoMean, crushMean
      }
    }
  ' "$RESULTS" > "$COMPARISON"
}

check_repo "$CRUSH_ROOT" "lean-crush"
[[ -f "$CRUSH_ROOT/.lake/build/lib/lean/Crush.olean" ]] ||
  die "local Crush is not built; run 'lake build Crush'"
if ! is_true "$RUN_AUTO" && ! is_true "$RUN_CRUSH"; then
  die "at least one of RUN_AUTO or RUN_CRUSH must be true"
fi

if is_true "$RUN_LEANHAMMER"; then
  check_repo "$HAMMER_REPO" "LeanHammer"
fi
if is_true "$RUN_LOOM" || is_true "$RUN_CASHMERE"; then
  check_repo "$LOOM_REPO" "Loom"
  check_ref "$LOOM_REPO" "$LOOM_AUTO_REF"
  check_ref "$LOOM_REPO" "$LOOM_CRUSH_REF"
fi
if is_true "$RUN_VELVET"; then
  check_repo "$VELVET_REPO" "Velvet"
  check_ref "$VELVET_REPO" "$VELVET_AUTO_REF"
  check_ref "$VELVET_REPO" "$VELVET_CRUSH_REF"
fi

mkdir -p "$OUT_DIR/logs"
printf 'suite\tbackend\tref\tcommit\ttoolchain\trepeat\tfile\tproof\tvc\tgoal_hash\tstatus\tcategory\tmilliseconds\tmessage\tgoal\n' > "$RESULTS"
printf 'suite\tbackend\trepeat\tfile\texit_code\twall_seconds\tvc_count\ttruncated\tmessage\n' > "$RUNS"
printf 'suite\tbackend\tref\tcommit\ttoolchain\tsolver\ttimeout\tvc_max_heartbeats\tcrush_trust\tcrush_commit\tcrush_dirty\tworktree\n' > "$METADATA"

if is_true "$RUN_LEANHAMMER"; then
  printf 'Running LeanHammer focused suite\n'
  hammer_out="$OUT_DIR/leanhammer"
  if HAMMER_REPO="$HAMMER_REPO" REPEATS="$REPEATS" OUT_DIR="$hammer_out" \
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
        "$(git -C "$LOOM_REPO" rev-parse "${LOOM_AUTO_REF}^{commit}")" ]] ||
      die "LOOM_AUTO_TREE is not at $LOOM_AUTO_REF"
    prepare_tree "loom-auto" "$loom_auto_tree" \
      CaseStudies.Tactic CaseStudies.Cashmere.Syntax_Cashmere
  fi
  if is_true "$RUN_CRUSH"; then
    if [[ -n "$LOOM_CRUSH_TREE" ]]; then
      loom_crush_tree="$(cd "$LOOM_CRUSH_TREE" && pwd)"
    else
      add_worktree "$LOOM_REPO" "$LOOM_CRUSH_REF" "loom-crush"
      loom_crush_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$loom_crush_tree" rev-parse HEAD)" == \
        "$(git -C "$LOOM_REPO" rev-parse "${LOOM_CRUSH_REF}^{commit}")" ]] ||
      die "LOOM_CRUSH_TREE is not at $LOOM_CRUSH_REF"
    prepare_tree "loom-crush" "$loom_crush_tree" \
      CaseStudies.Tactic CaseStudies.Cashmere.Syntax_Cashmere
  fi
fi

if is_true "$RUN_LOOM"; then
  if is_true "$RUN_AUTO"; then
    record_metadata "loom" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
    run_fixture "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
  fi
  if is_true "$RUN_CRUSH"; then
    record_metadata "loom" "crush" "$LOOM_CRUSH_REF" "$loom_crush_tree"
    run_fixture "crush" "$LOOM_CRUSH_REF" "$loom_crush_tree"
  fi
fi

if is_true "$RUN_CASHMERE"; then
  if is_true "$RUN_AUTO"; then
    record_metadata "cashmere" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree"
    run_files "cashmere" "auto" "$LOOM_AUTO_REF" "$loom_auto_tree" "${CASHMERE_FILES[@]}"
  fi
  if is_true "$RUN_CRUSH"; then
    record_metadata "cashmere" "crush" "$LOOM_CRUSH_REF" "$loom_crush_tree"
    run_files "cashmere" "crush" "$LOOM_CRUSH_REF" "$loom_crush_tree" "${CASHMERE_FILES[@]}"
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
        "$(git -C "$VELVET_REPO" rev-parse "${VELVET_AUTO_REF}^{commit}")" ]] ||
      die "VELVET_AUTO_TREE is not at $VELVET_AUTO_REF"
    prepare_tree "velvet-auto" "$velvet_auto_tree" Velvet.Std
  fi
  if is_true "$RUN_CRUSH"; then
    if [[ -n "$VELVET_CRUSH_TREE" ]]; then
      velvet_crush_tree="$(cd "$VELVET_CRUSH_TREE" && pwd)"
    else
      add_worktree "$VELVET_REPO" "$VELVET_CRUSH_REF" "velvet-crush"
      velvet_crush_tree="$ADDED_WORKTREE"
    fi
    [[ "$(git -C "$velvet_crush_tree" rev-parse HEAD)" == \
        "$(git -C "$VELVET_REPO" rev-parse "${VELVET_CRUSH_REF}^{commit}")" ]] ||
      die "VELVET_CRUSH_TREE is not at $VELVET_CRUSH_REF"
    prepare_tree "velvet-crush" "$velvet_crush_tree" Velvet.Std
  fi
  if is_true "$RUN_AUTO"; then
    record_metadata "velvet" "auto" "$VELVET_AUTO_REF" "$velvet_auto_tree"
    run_files "velvet" "auto" "$VELVET_AUTO_REF" "$velvet_auto_tree" "${VELVET_FILES[@]}"
  fi
  if is_true "$RUN_CRUSH"; then
    record_metadata "velvet" "crush" "$VELVET_CRUSH_REF" "$velvet_crush_tree"
    run_files "velvet" "crush" "$VELVET_CRUSH_REF" "$velvet_crush_tree" "${VELVET_FILES[@]}"
  fi
fi

write_reports

printf '\nCorpus summary:\n'
column -t -s $'\t' "$SUMMARY" 2>/dev/null || cat "$SUMMARY"
printf '\nMatched-VC comparison:\n'
column -t -s $'\t' "$COMPARISON" 2>/dev/null || cat "$COMPARISON"
printf '\nResults: %s\n' "$OUT_DIR"

if [[ "$TRUNCATED_RUNS" -gt 0 ]]; then
  die "$TRUNCATED_RUNS benchmark run(s) were truncated before all VCs were emitted"
fi
