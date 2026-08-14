#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PLEAN_AUTO_TREE="${PLEAN_AUTO_TREE:-/private/tmp/PLean-auto/Src/PLean}"
PLEAN_CRUSH_TREE="${PLEAN_CRUSH_TREE:-$HOME/Downloads/P/Src/PLean}"
REPEATS="${REPEATS:-1}"
SOLVER="${SOLVER:-cvc5}"
TIMEOUT="${TIMEOUT:-5}"
CRUSH_TRUST="${CRUSH_TRUST:-trust}"
CRUSH_INST_FUEL="${CRUSH_INST_FUEL:-0}"
MAX_HEARTBEATS="${MAX_HEARTBEATS:-1000000}"
RUN_AUTO="${RUN_AUTO:-true}"
RUN_CRUSH="${RUN_CRUSH:-true}"
OUT_DIR="${OUT_DIR:-$CRUSH_ROOT/BenchmarkResults/plean-$(date +%Y%m%d-%H%M%S)}"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/lean-crush-plean.XXXXXX")"

RESULTS="$OUT_DIR/results.tsv"
RUNS="$OUT_DIR/runs.tsv"
METADATA="$OUT_DIR/metadata.tsv"
SUMMARY="$OUT_DIR/summary.tsv"
FILE_SUMMARY="$OUT_DIR/file-summary.tsv"
COMPARISON="$OUT_DIR/comparison.tsv"

PLEAN_FILES=(
  "Examples/ClockBound.lean"
  "Examples/Consensus.lean"
  "Examples/DistributedLock.lean"
  "Examples/LockServer.lean"
  "Examples/PingPongAuto.lean"
  "Examples/PingPongTrivial.lean"
  "Examples/RingLeader.lean"
  "Examples/ShardedKV.lean"
  "Examples/TwoPhaseCommit.lean"
)

if [[ -n "${PLEAN_CASES:-}" ]]; then
  read -r -a PLEAN_FILES <<< "$PLEAN_CASES"
fi

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

is_true() {
  [[ "$1" == "true" ]]
}

cleanup() {
  rm -rf "$TMP_ROOT"
}
trap cleanup EXIT INT TERM

check_tree() {
  local tree="$1"
  local label="$2"
  [[ -f "$tree/lakefile.lean" ]] || die "$label PLean tree not found at $tree"
}

write_prelude() {
  local output="$1"
  local backend="$2"

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option loom.solver "$SOLVER" in
    set_option loom.solver.smt.timeout $TIMEOUT in
    set_option pverify.cache false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  else
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option crush.backend "$SOLVER" in
    set_option crush.timeout $TIMEOUT in
    set_option crush.trust "$CRUSH_TRUST" in
    set_option crush.inst.fuel $CRUSH_INST_FUEL in
    set_option pverify.cache false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  fi

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.cachePp + row.cacheHash + row.cacheFs +
      row.smtPrep + row.smtAuto + row.smtSolver + row.smtAssign
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"

EOF
  else
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.cachePp + row.cacheHash + row.cacheFs +
      row.cacheClose + row.smtPrep + row.smtCrush
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"

EOF
  fi
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
    awk '
      /^[[:space:]]*@\[pverifyProof\][[:space:]]*$/ {
        renameTheorem = 1
        next
      }
      renameTheorem && /^theorem[[:space:]]+/ {
        line = $0
        name = line
        sub(/^theorem[[:space:]]+/, "", name)
        sub(/[[:space:]].*$/, "", name)
        sub(/^theorem[[:space:]]+[^[:space:]]+/,
            "theorem " name "_benchmark_disabled", line)
        print line
        renameTheorem = 0
        next
      }
      /^#pverify[[:space:]]+/ {
        sub(/^#pverify/, "#plean_bench_pverify")
        print
        print "#plean_bench_report"
        next
      }
      { print }
    ' >> "$output"
}

record_metadata() {
  local backend="$1"
  local tree="$2"
  local commit toolchain dirty diff_hash crush_commit crush_dirty
  commit="$(git -C "$tree" rev-parse HEAD)"
  toolchain="$(tr -d '\r\n' < "$tree/lean-toolchain")"
  dirty="false"
  diff_hash="-"
  crush_commit="-"
  crush_dirty="false"
  if [[ -n "$(git -C "$tree" status --porcelain)" ]]; then
    dirty="true"
    diff_hash="$(git -C "$tree" diff --binary | shasum -a 256 | awk '{print $1}')"
  fi
  if [[ "$backend" == "crush" ]]; then
    crush_commit="$(git -C "$CRUSH_ROOT" rev-parse HEAD)"
    if [[ -n "$(git -C "$CRUSH_ROOT" status --porcelain -- \
        . ':(exclude)BenchmarkResults')" ]]; then
      crush_dirty="true"
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$backend" "$commit" "$toolchain" "$dirty" "$diff_hash" "$SOLVER" \
    "$TIMEOUT" "$MAX_HEARTBEATS" "$CRUSH_TRUST" "$CRUSH_INST_FUEL" \
    "$crush_commit" "$crush_dirty" "$tree" >> "$METADATA"
}

append_markers() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  local log="$4"
  awk -v backend="$backend" -v repeat="$repeat" -v file="$file" '
    BEGIN { FS = " "; OFS = "\t" }
    {
      if (index($0, "[SMT]") > 0) passed[$2] = 1
      marker = index($0, "PLEAN_TIME\t")
      if (marker > 0) {
        line = substr($0, marker)
        split(line, result, "\t")
        names[++count] = result[2]
        nanos[result[2]] = result[3]
      }
    }
    END {
      for (i = 1; i <= count; i++) {
        name = names[i]
        status = passed[name] ? "pass" : "fail"
        category = passed[name] ? "-" : "tactic"
        printf "plean\t%s\t%s\t%s\t%s\t-\t%s\t%s\t%.3f\tfalse\t-\t-\n",
          backend, repeat, file, name, status, category, nanos[name] / 1000000
      }
    }
  ' "$log" >> "$RESULTS"
}

append_synthetic_records() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  local log="$4"
  local total smt marker_count marker_pass missing synthetic_pass i

  total="$(sed -nE 's/.*: ([0-9]+) obligations from.*/\1/p' "$log" | tail -n 1)"
  smt="$(sed -nE 's/.*: ([0-9]+) proved by SMT,.*/\1/p' "$log" | tail -n 1)"
  total="${total:-0}"
  smt="${smt:-0}"
  marker_count="$(awk '/PLEAN_TIME\t/ { n++ } END { print n + 0 }' "$log")"
  marker_pass="$(awk '/\[SMT\]/ { n++ } END { print n + 0 }' "$log")"
  missing=$((total - marker_count))
  if [[ "$missing" -le 0 ]]; then
    return
  fi
  synthetic_pass=$((smt - marker_pass))
  if [[ "$synthetic_pass" -lt 0 ]]; then
    synthetic_pass=0
  fi
  if [[ "$synthetic_pass" -gt "$missing" ]]; then
    synthetic_pass="$missing"
  fi
  for ((i = 1; i <= missing; i++)); do
    if [[ "$i" -le "$synthetic_pass" ]]; then
      printf 'plean\t%s\t%s\t%s\tpre_smt_%s\t-\tpass\t-\t0\ttrue\tclosed before backend timing\t-\n' \
        "$backend" "$repeat" "$file" "$i" >> "$RESULTS"
    else
      printf 'plean\t%s\t%s\t%s\tunmeasured_%s\t-\tfail\ttactic\t0\ttrue\tno backend timing record\t-\n' \
        "$backend" "$repeat" "$file" "$i" >> "$RESULTS"
    fi
  done
}

run_file() {
  local backend="$1"
  local tree="$2"
  local repeat="$3"
  local file="$4"
  local generated="$TMP_ROOT/generated/$backend/${file//\//_}"
  local log="$OUT_DIR/logs/$backend/${file//\//_}.$repeat.log"
  local started elapsed exit_code total

  mkdir -p "$(dirname "$generated")" "$(dirname "$log")"
  write_benchmark_file "$tree/$file" "$generated" "$backend"
  printf '%-5s run %s: %s\n' "$backend" "$repeat" "$file"
  started="$(date +%s)"
  if [[ "$backend" == "crush" ]]; then
    "$CRUSH_ROOT/scripts/with-local-crush.sh" "$tree" \
      "-DmaxHeartbeats=$MAX_HEARTBEATS" \
      "-Dpverify.cache=false" "$generated" > "$log" 2>&1
  else
    (cd "$tree" && lake env lean \
      "-DmaxHeartbeats=$MAX_HEARTBEATS" \
      "-Dpverify.cache=false" "$generated") > "$log" 2>&1
  fi
  exit_code=$?
  elapsed="$(( $(date +%s) - started ))"
  append_markers "$backend" "$repeat" "$file" "$log"
  append_synthetic_records "$backend" "$repeat" "$file" "$log"
  total="$(sed -nE 's/.*: ([0-9]+) obligations from.*/\1/p' "$log" | tail -n 1)"
  printf 'plean\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$backend" "$repeat" "$file" "$exit_code" "$elapsed" "${total:-0}" >> "$RUNS"
}

write_reports() {
  awk -F '\t' '
    BEGIN {
      OFS = "\t"
      print "suite", "backend", "attempted", "passed", "failed", "pass_pct",
            "total_ms", "mean_ms", "min_ms", "max_ms"
    }
    NR > 1 {
      key = $1 SUBSEP $2
      seen[key] = 1
      attempted[key]++
      total[key] += $9
      if (!(key in minimum) || $9 < minimum[key]) minimum[key] = $9
      if (!(key in maximum) || $9 > maximum[key]) maximum[key] = $9
      if ($7 == "pass") passed[key]++
    }
    END {
      for (key in seen) {
        split(key, p, SUBSEP)
        failed = attempted[key] - passed[key]
        pct = attempted[key] ? 100 * passed[key] / attempted[key] : 0
        printf "%s\t%s\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\n",
          p[1], p[2], attempted[key], passed[key], failed, pct,
          total[key], attempted[key] ? total[key] / attempted[key] : 0,
          minimum[key], maximum[key]
      }
    }
  ' "$RESULTS" > "$SUMMARY"

  awk -F '\t' '
    BEGIN {
      OFS = "\t"
      print "suite", "backend", "file", "attempted", "passed", "failed",
            "pass_pct", "total_ms", "mean_ms", "min_ms", "max_ms"
    }
    NR > 1 {
      key = $1 SUBSEP $2 SUBSEP $4
      seen[key] = 1
      attempted[key]++
      total[key] += $9
      if (!(key in minimum) || $9 < minimum[key]) minimum[key] = $9
      if (!(key in maximum) || $9 > maximum[key]) maximum[key] = $9
      if ($7 == "pass") passed[key]++
    }
    END {
      for (key in seen) {
        split(key, p, SUBSEP)
        failed = attempted[key] - passed[key]
        pct = attempted[key] ? 100 * passed[key] / attempted[key] : 0
        printf "%s\t%s\t%s\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\n",
          p[1], p[2], p[3], attempted[key], passed[key], failed, pct,
          total[key], total[key] / attempted[key], minimum[key], maximum[key]
      }
    }
  ' "$RESULTS" > "$FILE_SUMMARY"

  awk -F '\t' -v repeats="$REPEATS" '
    BEGIN {
      OFS = "\t"
      print "suite", "shared_vcs", "auto_only_wins", "crush_only_wins",
            "both_solved", "neither_solved", "auto_mean_ms", "crush_mean_ms"
    }
    NR > 1 {
      vc = $1 SUBSEP $4 SUBSEP $5
      run = vc SUBSEP $2 SUBSEP $3
      runSeen[run] = 1
      runMs[run] += $9
      if ($7 != "pass") runFailed[run] = 1
      suites[$1] = 1
    }
    END {
      for (run in runSeen) {
        split(run, p, SUBSEP)
        vc = p[1] SUBSEP p[2] SUBSEP p[3]
        backend = p[4]
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

check_tree "$PLEAN_AUTO_TREE" "auto"
check_tree "$PLEAN_CRUSH_TREE" "Crush"
[[ -f "$CRUSH_ROOT/.lake/build/lib/lean/Crush.olean" ]] ||
  die "local Crush is not built; run 'lake build Crush'"
if ! is_true "$RUN_AUTO" && ! is_true "$RUN_CRUSH"; then
  die "at least one backend must be enabled"
fi

mkdir -p "$OUT_DIR/logs"
printf 'suite\tbackend\trepeat\tfile\tproof\tgoal_hash\tstatus\tcategory\tmilliseconds\tsynthetic\tmessage\tgoal\n' > "$RESULTS"
printf 'suite\tbackend\trepeat\tfile\texit_code\twall_seconds\tvc_count\n' > "$RUNS"
printf 'backend\tcommit\ttoolchain\tdirty\tdiff_sha256\tsolver\ttimeout\tmax_heartbeats\tcrush_trust\tcrush_inst_fuel\tcrush_commit\tcrush_dirty\ttree\n' > "$METADATA"

if is_true "$RUN_AUTO"; then
  record_metadata "auto" "$PLEAN_AUTO_TREE"
fi
if is_true "$RUN_CRUSH"; then
  record_metadata "crush" "$PLEAN_CRUSH_TREE"
fi

for repeat in $(seq 1 "$REPEATS"); do
  for file in "${PLEAN_FILES[@]}"; do
    if is_true "$RUN_AUTO"; then
      run_file "auto" "$PLEAN_AUTO_TREE" "$repeat" "$file"
    fi
    if is_true "$RUN_CRUSH"; then
      run_file "crush" "$PLEAN_CRUSH_TREE" "$repeat" "$file"
    fi
  done
done

write_reports
printf '\nPLean summary:\n'
column -t -s $'\t' "$SUMMARY" 2>/dev/null || cat "$SUMMARY"
printf '\nMatched-VC comparison:\n'
column -t -s $'\t' "$COMPARISON" 2>/dev/null || cat "$COMPARISON"
printf '\nResults: %s\n' "$OUT_DIR"
