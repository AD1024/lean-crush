#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRUSH_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/benchmark-common.sh"

PLEAN_AUTO_TREE="${PLEAN_AUTO_TREE:-}"
PLEAN_CRUSH_TREE="${PLEAN_CRUSH_TREE:-}"
PLEAN_DUPER_TREE="${PLEAN_DUPER_TREE:-}"
PLEAN_GRIND_TREE="${PLEAN_GRIND_TREE:-}"
PLEAN_AUTO_REPO_URL="${PLEAN_AUTO_REPO_URL:-https://github.com/AD1024/P.git}"
PLEAN_AUTO_REV="${PLEAN_AUTO_REV:-be39726723e71f9aa1e02c6cfeeae9b0c31b8947}"
PLEAN_CRUSH_REPO_URL="${PLEAN_CRUSH_REPO_URL:-https://github.com/AD1024/P.git}"
PLEAN_CRUSH_REV="${PLEAN_CRUSH_REV:-9c098b4c5ad32faf2a022929b6726d2a182a9e1d}"
PLEAN_DUPER_REPO_URL="${PLEAN_DUPER_REPO_URL:-https://github.com/AD1024/P.git}"
PLEAN_DUPER_REV="${PLEAN_DUPER_REV:-3557f1f0fa5246ee88fcde3776f3973349049968}"
PLEAN_GRIND_REPO_URL="${PLEAN_GRIND_REPO_URL:-$PLEAN_CRUSH_REPO_URL}"
PLEAN_GRIND_REV="${PLEAN_GRIND_REV:-$PLEAN_CRUSH_REV}"
BENCHMARK_SOURCE_CACHE="${BENCHMARK_SOURCE_CACHE:-$CRUSH_ROOT/BenchmarkResults/sources}"
REPEATS="${REPEATS:-1}"
SOLVER="${SOLVER:-cvc5}"
TIMEOUT="${TIMEOUT:-5}"
DUPER_TIMEOUT="${DUPER_TIMEOUT:-1}"
CRUSH_MODES="${CRUSH_MODES:-verify core alethe portfolio}"
CRUSH_PROFILE="${CRUSH_PROFILE:-true}"
CRUSH_INST_FUEL="${CRUSH_INST_FUEL:-0}"
MAX_HEARTBEATS="${MAX_HEARTBEATS:-1000000}"
MAX_RECURSION_DEPTH="${MAX_RECURSION_DEPTH:-1000000}"
GRIND_SPLITS="${GRIND_SPLITS:-20}"
DUPER_MAX_HEARTBEATS="${DUPER_MAX_HEARTBEATS:-20000}"
DUPER_FILE_CPU_SECONDS="${DUPER_FILE_CPU_SECONDS:-0}"
RUN_AUTO="${RUN_AUTO:-true}"
RUN_CRUSH="${RUN_CRUSH:-true}"
RUN_DUPER="${RUN_DUPER:-false}"
RUN_GRIND="${RUN_GRIND:-true}"
USE_MATHLIB_CACHE="${USE_MATHLIB_CACHE:-true}"
PREPARE_TREES="${PREPARE_TREES:-true}"
RESUME="${RESUME:-false}"
OUT_DIR="${OUT_DIR:-$CRUSH_ROOT/BenchmarkResults/plean-$(date +%Y%m%d-%H%M%S)}"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/lean-crush-plean.XXXXXX")"

RESULTS="$OUT_DIR/results.tsv"
RUNS="$OUT_DIR/runs.tsv"
METADATA="$OUT_DIR/metadata.tsv"
SUMMARY="$OUT_DIR/summary.tsv"
FILE_SUMMARY="$OUT_DIR/file-summary.tsv"
COMPARISON="$OUT_DIR/comparison.tsv"
MEASUREMENTS="$OUT_DIR/measurements.tsv"
PROFILES="$OUT_DIR/profile-events.tsv"
CHECKPOINTS="$OUT_DIR/checkpoints.tsv"
WORKTREES=()
PROVISIONED_TREE=""
HARNESS_FAILURES=0
SOLVER_GUARD_DIR="$TMP_ROOT/solver-guard"

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

is_crush_lane() {
  [[ "$1" == crush-* ]]
}

validate_nat() {
  local name="$1"
  local value="$2"
  [[ "$value" =~ ^[0-9]+$ ]] ||
    die "$name must be a nonnegative integer, got: $value"
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
      verify|core|alethe|portfolio) CRUSH_LANES+=("crush-$mode") ;;
      *) die "unknown Crush measurement mode: $mode" ;;
    esac
  done
fi

cleanup() {
  local entry repo path
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

check_tree() {
  local tree="$1"
  local label="$2"
  [[ -f "$tree/lakefile.lean" ]] || die "$label PLean tree not found at $tree"
}

provision_tree() {
  local label="$1"
  local url="$2"
  local revision="$3"
  local cache_name="$4"
  local checkout_name="$5"
  local repo checkout

  repo="$(benchmark_ensure_repo "$label" "$url" "$revision" \
    "$BENCHMARK_SOURCE_CACHE/$cache_name")" ||
    die "failed to provision $label"
  checkout="$TMP_ROOT/$checkout_name"
  benchmark_add_worktree "$repo" "$revision" "$checkout" >/dev/null ||
    die "failed to check out $label at $revision"
  WORKTREES+=("$repo|$checkout")
  PROVISIONED_TREE="$checkout/Src/PLean"
}

prepare_solver_guard() {
  mkdir -p "$SOLVER_GUARD_DIR"
  cat > "$SOLVER_GUARD_DIR/solver-disabled" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "${0##*/}" >> "${PLEAN_SOLVER_GUARD_LOG:?}"
exit 97
EOF
  chmod +x "$SOLVER_GUARD_DIR/solver-disabled"
  ln -sf solver-disabled "$SOLVER_GUARD_DIR/cvc5"
  ln -sf solver-disabled "$SOLVER_GUARD_DIR/z3"
  ln -sf solver-disabled "$SOLVER_GUARD_DIR/bitwuzla"
}

validate_grind_tree() {
  local tree="$1"
  local tactic="$tree/PLean/Verify/Tactic.lean"
  local expected

  expected="$(grep -F -c "grind (splits := $GRIND_SPLITS)" "$tactic")"
  [[ "$expected" -eq 3 ]] ||
    die "grind PLean tree is not patched for GRIND_SPLITS=$GRIND_SPLITS"
  if grep -Fq 'all_goals crush [*]' "$tactic"; then
    die "grind PLean tree still contains a direct Crush backend call"
  fi
}

patch_grind_tree() {
  local tree="$1"
  local patch_file="$TMP_ROOT/plean-grind.patch"

  sed "s/@GRIND_SPLITS@/$GRIND_SPLITS/g" \
    "$SCRIPT_DIR/patches/plean-grind.patch.in" > "$patch_file"
  if ! patch -d "$tree" -p1 --forward --batch < "$patch_file"; then
    die "failed to apply the pinned PLean grind backend patch"
  fi
  validate_grind_tree "$tree"
}

prepare_tree() {
  local label="$1"
  local tree="$2"
  local log="$OUT_DIR/build-$label.log"
  local guard_log="$OUT_DIR/solver-guard-build-$label.log"

  printf 'Building %s PLean tree\n' "$label"
  if ! (cd "$tree" && lake env printenv LEAN_PATH) \
      > "$OUT_DIR/dependencies-$label.log" 2>&1; then
    tail -n 80 "$OUT_DIR/dependencies-$label.log" >&2
    die "$label PLean dependency setup failed"
  fi
  if is_true "$USE_MATHLIB_CACHE"; then
    printf 'Fetching cached dependencies for %s PLean tree\n' "$label"
    if ! benchmark_fetch_cache "$tree" "$OUT_DIR/cache-$label.log"; then
      printf 'warning: Mathlib cache unavailable for %s PLean tree\n' \
        "$label" >&2
    fi
  fi
  if [[ "$label" == "crush" ]]; then
    benchmark_sync_crush_sources "$CRUSH_ROOT" "$tree" ||
      die "failed to synchronize local Crush sources"
  fi
  if [[ "$label" == "grind" ]]; then
    if ! (cd "$tree" && PATH="$SOLVER_GUARD_DIR:$PATH" \
        PLEAN_SOLVER_GUARD_LOG="$guard_log" lake build) > "$log" 2>&1; then
      tail -n 80 "$log" >&2
      die "$label PLean build failed; see $log"
    fi
    if [[ -s "$guard_log" ]]; then
      die "grind PLean build attempted to invoke an external solver"
    fi
  elif ! (cd "$tree" && lake build) > "$log" 2>&1; then
    tail -n 80 "$log" >&2
    die "$label PLean build failed; see $log"
  fi
}

write_prelude() {
  local output="$1"
  local backend="$2"
  local trust reconstruct

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option loom.solver "$SOLVER" in
    set_option loom.solver.smt.timeout $TIMEOUT in
    set_option pverify.cache false in
    set_option pverify.failOnIncomplete false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  elif is_crush_lane "$backend"; then
    trust="$(crush_lane_trust "$backend")"
    reconstruct="$(crush_lane_reconstruct "$backend")"
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option crush.backend "$SOLVER" in
    set_option crush.timeout $TIMEOUT in
    set_option crush.trust "$trust" in
    set_option crush.reconstruct "$reconstruct" in
    set_option crush.inst.fuel $CRUSH_INST_FUEL in
    set_option crush.profile $CRUSH_PROFILE in
    set_option crush.profile.machine true in
    set_option pverify.cache false in
    set_option pverify.failOnIncomplete false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  elif [[ "$backend" == "grind" ]]; then
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option pverify.cache false in
    set_option pverify.failOnIncomplete false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  else
    cat >> "$output" <<EOF

macro "#plean_bench_pverify " name:ident : command =>
  \`(command|
    set_option duper.maxSaturationTime $DUPER_TIMEOUT in
    set_option pverify.cache false in
    set_option pverify.failOnIncomplete false in
    set_option pverify.profile true in
    #pverify \$name)
EOF
  fi

  cat >> "$output" <<'EOF'

open Lean Elab Command

private def pleanBenchContains (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

private def pleanBenchDiagnosticCategory (obligation : String) : IO String := do
  let diag ← PLean.getDiag obligation
  let raw := match diag.smt with
    | some msg => msg
    | none => diag.tac.getD ""
  let msg := raw.toLower
  if pleanBenchContains msg "timed out" ||
      pleanBenchContains msg "timeout at" ||
      pleanBenchContains msg "deterministic) timeout" ||
      pleanBenchContains msg "solver exited without a verdict" ||
      pleanBenchContains msg "heartbeat" ||
      pleanBenchContains msg "maxsaturation" ||
      pleanBenchContains msg "saturation time" ||
      pleanBenchContains msg "saturation limit" then
    return "timeout"
  if pleanBenchContains msg "translation" ||
      pleanBenchContains msg "unsupported" ||
      pleanBenchContains msg "higher-order" ||
      pleanBenchContains msg "cannot translate" ||
      pleanBenchContains msg "cannot encode" then
    return "translation"
  return "tactic"

private def pleanBenchReportDiagnostic (obligation : String) : IO Unit := do
  let category ← pleanBenchDiagnosticCategory obligation
  IO.println s!"PLEAN_DIAG\t{obligation}\t{category}"

EOF

  if [[ "$backend" == "auto" ]]; then
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.cachePp + row.cacheHash + row.cacheFs +
      row.smtPrep + row.smtAuto + row.smtSolver + row.smtAssign
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"
    liftM (pleanBenchReportDiagnostic row.obligation)

EOF
  elif is_crush_lane "$backend"; then
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.cachePp + row.cacheHash + row.cacheFs +
      row.cacheClose + row.smtPrep + row.smtCrush
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"
    liftM (pleanBenchReportDiagnostic row.obligation)

EOF
  elif [[ "$backend" == "grind" ]]; then
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.smtPrep + row.smtCrush
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"
    liftM (pleanBenchReportDiagnostic row.obligation)

EOF
  else
    cat >> "$output" <<'EOF'

open Lean Elab Command

elab "#plean_bench_report" : command => do
  let profile <- liftM (PLean.Verify.Profile.stateRef.get : IO _)
  for row in profile.rows do
    let nanos := row.cachePp + row.cacheHash + row.cacheFs +
      row.cacheClose + row.smtPrep + row.smtDuper
    IO.println s!"PLEAN_TIME\t{row.obligation}\t{nanos}"
    liftM (pleanBenchReportDiagnostic row.obligation)

EOF
  fi
  printf '\n-- PLEAN_BENCH_PRELUDE_END\n' >> "$output"
}

write_benchmark_file() {
  local source="$1"
  local output="$2"
  local backend="$3"
  local last_import max_heartbeats

  last_import="$(awk '/^import / { line = NR } END { print line + 0 }' "$source")"
  [[ "$last_import" -gt 0 ]] || die "no imports found in $source"
  max_heartbeats="$MAX_HEARTBEATS"
  if [[ "$backend" == "duper" ]]; then
    max_heartbeats="$DUPER_MAX_HEARTBEATS"
  fi
  head -n "$last_import" "$source" > "$output"
  write_prelude "$output" "$backend"

  tail -n "+$((last_import + 1))" "$source" |
    awk -v maxHeartbeats="$max_heartbeats" '
      function emitPendingOption() {
        if (pendingOption != "") {
          print pendingOption
          pendingOption = ""
        }
      }
      skipManualBody {
        if ($0 ~ /^[^[:space:]]/) {
          skipManualBody = 0
        } else {
          next
        }
      }
      manualHeader {
        line = $0
        if (!manualTheorem) {
          if (line ~ /^[[:space:]]*$/) next
          if (line !~ /^theorem[[:space:]]+/) {
            print "error: expected theorem after @[pverifyProof]" > "/dev/stderr"
            exit 2
          }
          manualTheorem = 1
        }
        if (line ~ /:= by/) {
          manualHeader = 0
          manualTheorem = 0
          skipManualBody = 1
        }
        next
      }
      /^[[:space:]]*set_option[[:space:]]+maxHeartbeats[[:space:]]+[0-9]+[[:space:]]+in[[:space:]]*$/ {
        emitPendingOption()
        sub(/maxHeartbeats[[:space:]]+[0-9]+/,
            "maxHeartbeats " maxHeartbeats)
        pendingOption = $0
        next
      }
      /^[[:space:]]*@\[pverifyProof\][[:space:]]*$/ {
        pendingOption = ""
        manualHeader = 1
        next
      }
      /^#pverify[[:space:]]+/ {
        emitPendingOption()
        sub(/^#pverify/, "#plean_bench_pverify")
        print
        print "#plean_bench_report"
        next
      }
      {
        emitPendingOption()
        print
      }
      END {
        emitPendingOption()
        if (manualHeader) {
          print "error: unterminated @[pverifyProof] declaration" > "/dev/stderr"
          exit 2
        }
      }
    ' >> "$output"
}

record_metadata() {
  local backend="$1"
  local tree="$2"
  local commit toolchain dirty diff_hash crush_commit duper_commit crush_dirty
  local max_heartbeats file_cpu_seconds trust reconstruct grind_splits
  commit="$(git -C "$tree" rev-parse HEAD)"
  toolchain="$(tr -d '\r\n' < "$tree/lean-toolchain")"
  dirty="false"
  diff_hash="-"
  crush_commit="-"
  duper_commit="-"
  crush_dirty="false"
  max_heartbeats="$MAX_HEARTBEATS"
  file_cpu_seconds="0"
  if [[ "$backend" == "duper" ]]; then
    max_heartbeats="$DUPER_MAX_HEARTBEATS"
    file_cpu_seconds="$DUPER_FILE_CPU_SECONDS"
  fi
  if [[ -n "$(git -C "$tree" status --porcelain)" ]]; then
    dirty="true"
    diff_hash="$(git -C "$tree" diff --binary | shasum -a 256 | awk '{print $1}')"
  fi
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
  grind_splits="-"
  if [[ "$backend" == "grind" ]]; then
    grind_splits="$GRIND_SPLITS"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$backend" "$commit" "$toolchain" "$dirty" "$diff_hash" "$SOLVER" \
    "$TIMEOUT" "$DUPER_TIMEOUT" "$max_heartbeats" "$MAX_RECURSION_DEPTH" \
    "$file_cpu_seconds" "$trust" "$reconstruct" "$CRUSH_INST_FUEL" \
    "$crush_commit" "$duper_commit" "$crush_dirty" "$tree" "$CRUSH_PROFILE" \
    "$grind_splits" \
    >> "$METADATA"
}

append_markers() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  local log="$4"
  awk -v backend="$backend" -v repeat="$repeat" -v file="$file" \
      -v measurements="$MEASUREMENTS" '
    BEGIN { FS = " "; OFS = "\t" }
    {
      if (index($0, "[SMT]") > 0) passed[$2] = 1
      marker = index($0, "PLEAN_DIAG\t")
      if (marker > 0) {
        line = substr($0, marker)
        split(line, result, "\t")
        categories[result[2]] = result[3]
      }
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
        failureCategory = (name in categories) ? categories[name] : "tactic"
        category = passed[name] ? "-" : failureCategory
        printf "plean\t%s\t%s\t%s\t%s\t-\t%s\t%s\t%.3f\tfalse\t-\t-\n",
          backend, repeat, file, name, status, category, nanos[name] / 1000000
        vcKey = file "|" name
        printf("plean\t%s\t%s\t%s\t%s\t%s\t%.3f\t-\n",
          backend, repeat, vcKey, status, category,
          nanos[name] / 1000000) >> measurements
      }
    }
  ' "$log" >> "$RESULTS"
}

append_profile_records() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  local log="$4"

  awk -v lane="$backend" -v repeat="$repeat" -v file="$file" \
      -v profiles="$PROFILES" '
    BEGIN { FS = OFS = "\t" }
    {
      marker = index($0, "CRUSH_PROFILE\t")
      if (marker == 0) next
      line = substr($0, marker)
      split(line, profile, "\t")
      vcKey = file "|" profile[3]
      print "plean", lane, repeat, vcKey, profile[3], profile[4],
            profile[5], profile[6], profile[7], profile[8], profile[9],
            profile[10] >> profiles
    }
  ' "$log"
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
      printf 'plean\t%s\t%s\t%s|pre_smt_%s\tpass\t-\t0\tclosed before backend timing\n' \
        "$backend" "$repeat" "$file" "$i" >> "$MEASUREMENTS"
    else
      printf 'plean\t%s\t%s\t%s\tunmeasured_%s\t-\tfail\ttactic\t0\ttrue\tno backend timing record\t-\n' \
        "$backend" "$repeat" "$file" "$i" >> "$RESULTS"
      printf 'plean\t%s\t%s\t%s|unmeasured_%s\tfail\ttactic\t0\tno backend timing record\n' \
        "$backend" "$repeat" "$file" "$i" >> "$MEASUREMENTS"
    fi
  done
}

checkpoint_complete() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  is_true "$RESUME" || return 1
  awk -F '\t' -v backend="$backend" -v repeat="$repeat" -v file="$file" '
    NR > 1 && $1 == backend && $2 == repeat && $3 == file { found = 1 }
    END { exit !found }
  ' "$CHECKPOINTS"
}

remove_checkpoint_rows() {
  local backend="$1"
  local repeat="$2"
  local file="$3"
  local temporary="$OUT_DIR/.resume.$$.tsv"
  awk -F '\t' -v OFS='\t' -v backend="$backend" -v repeat="$repeat" \
    -v file="$file" \
    'NR == 1 || !($2 == backend && $3 == repeat && $4 == file)' \
    "$RESULTS" > "$temporary" && mv "$temporary" "$RESULTS"
  awk -F '\t' -v OFS='\t' -v backend="$backend" -v repeat="$repeat" \
    -v file="$file" \
    'NR == 1 || !($2 == backend && $3 == repeat && $4 == file)' \
    "$RUNS" > "$temporary" && mv "$temporary" "$RUNS"
  awk -F '\t' -v OFS='\t' -v backend="$backend" -v repeat="$repeat" \
    -v file="$file" '
      NR == 1 || !($2 == backend && $3 == repeat &&
        substr($4, 1, length(file) + 1) == file "|")
    ' "$MEASUREMENTS" > "$temporary" && mv "$temporary" "$MEASUREMENTS"
  awk -F '\t' -v OFS='\t' -v backend="$backend" -v repeat="$repeat" \
    -v file="$file" '
      NR == 1 || !($2 == backend && $3 == repeat &&
        substr($4, 1, length(file) + 1) == file "|")
    ' "$PROFILES" > "$temporary" && mv "$temporary" "$PROFILES"
  awk -F '\t' -v OFS='\t' -v backend="$backend" -v repeat="$repeat" \
    -v file="$file" \
    'NR == 1 || !($1 == backend && $2 == repeat && $3 == file)' \
    "$CHECKPOINTS" > "$temporary" && mv "$temporary" "$CHECKPOINTS"
}

run_file() {
  local backend="$1"
  local tree="$2"
  local repeat="$3"
  local file="$4"
  local generated="$TMP_ROOT/generated/$backend/${file//\//_}"
  local log="$OUT_DIR/logs/$backend/${file//\//_}.$repeat.log"
  local started elapsed exit_code total max_heartbeats cpu_limited message
  local prelude_end prelude_errors guard_log

  if checkpoint_complete "$backend" "$repeat" "$file"; then
    printf 'checkpoint: skipping %-5s run %s: %s\n' \
      "$backend" "$repeat" "$file"
    return
  fi
  if is_true "$RESUME"; then
    remove_checkpoint_rows "$backend" "$repeat" "$file"
  fi

  mkdir -p "$(dirname "$generated")" "$(dirname "$log")"
  write_benchmark_file "$tree/$file" "$generated" "$backend"
  max_heartbeats="$MAX_HEARTBEATS"
  if [[ "$backend" == "duper" ]]; then
    max_heartbeats="$DUPER_MAX_HEARTBEATS"
  fi
  printf '%-5s run %s: %s\n' "$backend" "$repeat" "$file"
  started="$(date +%s)"
  if is_crush_lane "$backend"; then
    "$CRUSH_ROOT/scripts/with-local-crush.sh" "$tree" \
      "-DElab.async=false" \
      "-DmaxHeartbeats=$max_heartbeats" \
      "-DmaxRecDepth=$MAX_RECURSION_DEPTH" \
      "-Dpverify.cache=false" "$generated" > "$log" 2>&1
  elif [[ "$backend" == "duper" && "$DUPER_FILE_CPU_SECONDS" -gt 0 ]]; then
    (
      ulimit -t "$DUPER_FILE_CPU_SECONDS"
      cd "$tree"
      lake env lean \
        "-DElab.async=false" \
        "-DmaxHeartbeats=$max_heartbeats" \
        "-DmaxRecDepth=$MAX_RECURSION_DEPTH" \
        "-Dpverify.cache=false" "$generated"
    ) > "$log" 2>&1
  elif [[ "$backend" == "grind" ]]; then
    guard_log="$log.solver-guard"
    (cd "$tree" && PATH="$SOLVER_GUARD_DIR:$PATH" \
      PLEAN_SOLVER_GUARD_LOG="$guard_log" lake env lean \
      "-DElab.async=false" \
      "-DmaxHeartbeats=$max_heartbeats" \
      "-DmaxRecDepth=$MAX_RECURSION_DEPTH" \
      "-Dpverify.cache=false" "$generated") > "$log" 2>&1
  else
    (cd "$tree" && lake env lean \
      "-DElab.async=false" \
      "-DmaxHeartbeats=$max_heartbeats" \
      "-DmaxRecDepth=$MAX_RECURSION_DEPTH" \
      "-Dpverify.cache=false" "$generated") > "$log" 2>&1
  fi
  exit_code=$?
  elapsed="$(( $(date +%s) - started ))"
  append_markers "$backend" "$repeat" "$file" "$log"
  append_profile_records "$backend" "$repeat" "$file" "$log"
  append_synthetic_records "$backend" "$repeat" "$file" "$log"
  total="$(sed -nE 's/.*: ([0-9]+) obligations from.*/\1/p' "$log" | tail -n 1)"
  prelude_end="$(grep -nF -- '-- PLEAN_BENCH_PRELUDE_END' "$generated" |
    cut -d: -f1)"
  if [[ -z "$prelude_end" ]]; then
    prelude_errors=1
  else
    prelude_errors="$(
      grep -F "$generated:" "$log" |
        sed -nE 's/^.*:([0-9]+):[0-9]+: error[(:].*$/\1/p' |
        awk -v limit="$prelude_end" \
          '$1 <= limit { count++ } END { print count + 0 }'
    )"
  fi
  cpu_limited="false"
  message="-"
  if [[ "$backend" == "duper" && "$DUPER_FILE_CPU_SECONDS" -gt 0 &&
      "$exit_code" -eq 152 ]]; then
    cpu_limited="true"
    message="file did not complete within CPU limit"
  elif [[ "$backend" == "grind" && -s "$guard_log" ]]; then
    HARNESS_FAILURES=$((HARNESS_FAILURES + 1))
    message="grind lane attempted to invoke an external solver"
  elif [[ "$prelude_errors" -gt 0 ]]; then
    HARNESS_FAILURES=$((HARNESS_FAILURES + 1))
    message="benchmark prelude reported an error"
  elif [[ "$exit_code" -ne 0 ]]; then
    HARNESS_FAILURES=$((HARNESS_FAILURES + 1))
    message="generated benchmark file failed"
  fi
  printf 'plean\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$backend" "$repeat" "$file" "$exit_code" "$elapsed" "${total:-0}" \
    "$cpu_limited" "$message" >> "$RUNS"
  if [[ "$message" == "-" || "$cpu_limited" == "true" ]]; then
    printf '%s\t%s\t%s\n' "$backend" "$repeat" "$file" >> "$CHECKPOINTS"
  fi
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

}

if ! is_true "$RUN_AUTO" && ! is_true "$RUN_CRUSH" && ! is_true "$RUN_DUPER" &&
    ! is_true "$RUN_GRIND"; then
  die "at least one backend must be enabled"
fi
case "$RESUME" in
  true|false) ;;
  *) die "RESUME must be true or false" ;;
esac

mkdir -p "$OUT_DIR/logs"

validate_nat "GRIND_SPLITS" "$GRIND_SPLITS"
prepare_solver_guard

if is_true "$RUN_CRUSH"; then
  printf 'Building local Crush\n'
  if ! (cd "$CRUSH_ROOT" && lake build Crush) \
      > "$OUT_DIR/build-crush.log" 2>&1; then
    tail -n 80 "$OUT_DIR/build-crush.log" >&2
    die "local Crush build failed"
  fi
fi

if is_true "$RUN_AUTO"; then
  if [[ -z "$PLEAN_AUTO_TREE" ]]; then
    provision_tree "vanilla PLean" "$PLEAN_AUTO_REPO_URL" \
      "$PLEAN_AUTO_REV" "P-auto" "P-auto"
    PLEAN_AUTO_TREE="$PROVISIONED_TREE"
  else
    PLEAN_AUTO_TREE="$(cd "$PLEAN_AUTO_TREE" && pwd)"
  fi
  check_tree "$PLEAN_AUTO_TREE" "auto"
  if is_true "$PREPARE_TREES"; then
    prepare_tree "auto" "$PLEAN_AUTO_TREE"
  fi
fi

if is_true "$RUN_CRUSH"; then
  if [[ -z "$PLEAN_CRUSH_TREE" ]]; then
    if [[ -z "$PLEAN_CRUSH_REV" ]]; then
      die "set PLEAN_CRUSH_TREE, or publish the PLean Crush adaptation and set PLEAN_CRUSH_REV"
    fi
    provision_tree "Crush PLean" "$PLEAN_CRUSH_REPO_URL" \
      "$PLEAN_CRUSH_REV" "P-crush" "P-crush"
    PLEAN_CRUSH_TREE="$PROVISIONED_TREE"
  else
    PLEAN_CRUSH_TREE="$(cd "$PLEAN_CRUSH_TREE" && pwd)"
  fi
  check_tree "$PLEAN_CRUSH_TREE" "Crush"
  if is_true "$PREPARE_TREES"; then
    prepare_tree "crush" "$PLEAN_CRUSH_TREE"
  fi
fi

if is_true "$RUN_GRIND"; then
  if [[ -z "$PLEAN_GRIND_TREE" ]]; then
    provision_tree "grind PLean" "$PLEAN_GRIND_REPO_URL" \
      "$PLEAN_GRIND_REV" "P-crush" "P-grind"
    PLEAN_GRIND_TREE="$PROVISIONED_TREE"
  else
    PLEAN_GRIND_TREE="$(cd "$PLEAN_GRIND_TREE" && pwd)"
  fi
  check_tree "$PLEAN_GRIND_TREE" "grind"
  if is_true "$PREPARE_TREES"; then
    patch_grind_tree "$PLEAN_GRIND_TREE"
    prepare_tree "grind" "$PLEAN_GRIND_TREE"
  else
    validate_grind_tree "$PLEAN_GRIND_TREE"
  fi
fi

if is_true "$RUN_DUPER"; then
  if [[ -z "$PLEAN_DUPER_TREE" ]]; then
    provision_tree "Duper PLean" "$PLEAN_DUPER_REPO_URL" \
      "$PLEAN_DUPER_REV" "P-duper" "P-duper"
    PLEAN_DUPER_TREE="$PROVISIONED_TREE"
  else
    PLEAN_DUPER_TREE="$(cd "$PLEAN_DUPER_TREE" && pwd)"
  fi
  check_tree "$PLEAN_DUPER_TREE" "Duper"
  if is_true "$PREPARE_TREES"; then
    prepare_tree "duper" "$PLEAN_DUPER_TREE"
  fi
fi

initialize_tsv() {
  local file="$1"
  local header="$2"
  if ! is_true "$RESUME" || [[ ! -f "$file" ]]; then
    printf '%b\n' "$header" > "$file"
  fi
}

legacy_checkpoints=false
if is_true "$RESUME" && [[ ! -f "$CHECKPOINTS" ]]; then
  legacy_checkpoints=true
fi

initialize_tsv "$RESULTS" 'suite\tbackend\trepeat\tfile\tproof\tgoal_hash\tstatus\tcategory\tmilliseconds\tsynthetic\tmessage\tgoal'
initialize_tsv "$RUNS" 'suite\tbackend\trepeat\tfile\texit_code\twall_seconds\tvc_count\tcpu_limited\tmessage'
initialize_tsv "$METADATA" 'backend\tcommit\ttoolchain\tdirty\tdiff_sha256\tsolver\ttimeout\tduper_timeout\tmax_heartbeats\tmax_rec_depth\tfile_cpu_seconds\tcrush_trust\tcrush_reconstruct\tcrush_inst_fuel\tcrush_commit\tduper_commit\tcrush_dirty\ttree\tcrush_profile\tgrind_splits'
initialize_tsv "$MEASUREMENTS" 'suite\tlane\trepeat\tvc_key\tstatus\tcategory\tmilliseconds\tmessage'
initialize_tsv "$PROFILES" 'suite\tlane\trepeat\tvc_key\tdeclaration\tgoal_hash\toutcome\treplay\tdetail\ttotal_nanos\tphases\tmetrics'
initialize_tsv "$CHECKPOINTS" 'backend\trepeat\tfile'
if is_true "$legacy_checkpoints"; then
  awk -F '\t' -v OFS='\t' \
    'NR > 1 && ($9 == "-" || $8 == "true") { print $2, $3, $4 }' \
    "$RUNS" >> "$CHECKPOINTS"
fi

if is_true "$RUN_AUTO"; then
  record_metadata "auto" "$PLEAN_AUTO_TREE"
fi
if is_true "$RUN_CRUSH"; then
  for lane in "${CRUSH_LANES[@]}"; do
    record_metadata "$lane" "$PLEAN_CRUSH_TREE"
  done
fi
if is_true "$RUN_GRIND"; then
  record_metadata "grind" "$PLEAN_GRIND_TREE"
fi
if is_true "$RUN_DUPER"; then
  record_metadata "duper" "$PLEAN_DUPER_TREE"
fi

for repeat in $(seq 1 "$REPEATS"); do
  for file in "${PLEAN_FILES[@]}"; do
    if is_true "$RUN_AUTO"; then
      run_file "auto" "$PLEAN_AUTO_TREE" "$repeat" "$file"
    fi
    if is_true "$RUN_CRUSH"; then
      for lane in "${CRUSH_LANES[@]}"; do
        run_file "$lane" "$PLEAN_CRUSH_TREE" "$repeat" "$file"
      done
    fi
    if is_true "$RUN_GRIND"; then
      run_file "grind" "$PLEAN_GRIND_TREE" "$repeat" "$file"
    fi
    if is_true "$RUN_DUPER"; then
      run_file "duper" "$PLEAN_DUPER_TREE" "$repeat" "$file"
    fi
  done
done

write_reports
if ! python3 "$SCRIPT_DIR/benchmark-report.py" \
    --measurements "$MEASUREMENTS" --profiles "$PROFILES" \
    --out-dir "$OUT_DIR" --require-uniform-headline; then
  die "failed to generate measurement reports"
fi
printf '\nAll-VC headline summary:\n'
column -t -s $'\t' "$OUT_DIR/headline-summary.tsv" 2>/dev/null ||
  cat "$OUT_DIR/headline-summary.tsv"
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

missing_headline="$(
  awk -F '\t' 'NR > 1 { missing += $8 } END { print missing + 0 }' \
    "$OUT_DIR/headline-summary.tsv"
)"
if [[ "$missing_headline" -gt 0 ]]; then
  die "$missing_headline headline VC attempt(s) are missing"
fi
if [[ "$HARNESS_FAILURES" -gt 0 ]]; then
  die "$HARNESS_FAILURES benchmark file(s) failed harness validation"
fi
