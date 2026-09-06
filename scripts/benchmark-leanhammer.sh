#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
crush_root="$(cd "$script_dir/.." && pwd)"
source "$script_dir/benchmark-common.sh"

hammer_repo="${HAMMER_REPO:-}"
hammer_url="${HAMMER_REPO_URL:-https://github.com/AD1024/LeanHammer.git}"
hammer_rev="${HAMMER_REV:-df4dd13671412591d678eada250b04c030fd4d40}"
source_cache="${BENCHMARK_SOURCE_CACHE:-$crush_root/BenchmarkResults/sources}"
repeats="${REPEATS:-1}"
duper_timeout="${DUPER_TIMEOUT:-5}"
solver="${SOLVER:-cvc5}"
timeout="${TIMEOUT:-5}"
smt_timeout="${SMT_TIMEOUT:-$timeout}"
smt_mono="${SMT_MONO:-true}"
max_heartbeats="${MAX_HEARTBEATS:-1000000}"
max_rec_depth="${MAX_RECURSION_DEPTH:-1000000}"
crush_profile="${CRUSH_PROFILE:-true}"
use_mathlib_cache="${USE_MATHLIB_CACHE:-true}"
resume="${RESUME:-false}"
out_dir="${OUT_DIR:-$crush_root/BenchmarkResults/leanhammer-$(date +%Y%m%d-%H%M%S)}"
mkdir -p "$out_dir"
out_dir="$(cd "$out_dir" && pwd)"
results="$out_dir/results.tsv"
metadata="$out_dir/metadata.tsv"
summary="$out_dir/summary.tsv"
measurements="$out_dir/measurements.tsv"
profiles_out="$out_dir/profile-events.tsv"
checkpoints="$out_dir/checkpoints.tsv"
logs="$out_dir/logs"
read -r -a profiles <<< \
  "${PROFILES:-crush-only crush-verify crush-core crush-alethe crush-portfolio smt-only grind-only duper-only auto-duper aesop-auto-duper aesop-crush}"
tmp_root=""
managed_repo=""

runs_smt_lane=false
for candidate in "${profiles[@]}"; do
  if [[ "$candidate" == "smt-only" ]]; then
    runs_smt_lane=true
  fi
done
# lean-smt calls cvc5 through the in-process lean-cvc5 bindings, so it ignores
# SOLVER, Z3_BIN, and CVC5_BIN. Refuse to label its results with a solver it
# cannot use rather than reporting a mismatched comparison.
if [[ "$runs_smt_lane" == "true" && "$solver" != "cvc5" ]]; then
  printf 'error: the smt-only lane requires SOLVER=cvc5; got %s\n' "$solver" >&2
  exit 1
fi

cleanup() {
  if [[ -n "$managed_repo" && -n "$hammer_repo" ]]; then
    git -C "$managed_repo" worktree remove --force "$hammer_repo" \
      >/dev/null 2>&1 || true
  fi
  if [[ -n "$tmp_root" ]]; then
    rmdir "$tmp_root" >/dev/null 2>&1 || true
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

if [[ -z "$hammer_repo" ]]; then
  tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/lean-crush-hammer.XXXXXX")"
  managed_repo="$(benchmark_ensure_repo "LeanHammer" "$hammer_url" \
    "$hammer_rev" "$source_cache/LeanHammer")"
  hammer_repo="$tmp_root/LeanHammer"
  benchmark_add_worktree "$managed_repo" "$hammer_rev" "$hammer_repo" \
    >/dev/null
else
  hammer_repo="$(cd "$hammer_repo" && pwd)"
fi

if [[ ! -d "$hammer_repo/Benchmark/Cases" ]]; then
  printf 'error: LeanHammer benchmark not found at %s\n' "$hammer_repo" >&2
  exit 1
fi

mkdir -p "$logs"
printf 'Building local Crush\n'
if ! (cd "$crush_root" && lake build Crush) \
    > "$out_dir/build-crush.log" 2>&1; then
  tail -n 80 "$out_dir/build-crush.log" >&2
  printf 'error: local Crush build failed\n' >&2
  exit 1
fi

printf 'Preparing LeanHammer dependencies\n'
if ! (cd "$hammer_repo" && lake env printenv LEAN_PATH) \
    > "$out_dir/dependencies-leanhammer.log" 2>&1; then
  tail -n 80 "$out_dir/dependencies-leanhammer.log" >&2
  printf 'error: LeanHammer dependency setup failed\n' >&2
  exit 1
fi
if [[ "$use_mathlib_cache" == "true" ]]; then
  printf 'Fetching cached LeanHammer dependencies\n'
  if ! benchmark_fetch_cache "$hammer_repo" "$out_dir/cache-leanhammer.log"; then
    printf 'warning: Mathlib cache unavailable for LeanHammer; building from source\n' >&2
  fi
fi
if ! benchmark_sync_crush_sources "$crush_root" "$hammer_repo"; then
  exit 1
fi

printf 'Building LeanHammer benchmark\n'
if ! (cd "$hammer_repo" && lake build Benchmark.Harness) \
    > "$out_dir/build-leanhammer.log" 2>&1; then
  tail -n 80 "$out_dir/build-leanhammer.log" >&2
  printf 'error: LeanHammer benchmark build failed\n' >&2
  exit 1
fi

# lean-cvc5 sets `precompileModules`, so the `smt` tactic reaches cvc5 through
# FFI rather than by spawning a binary. A standalone `lean` process does not
# load that library on its own, and the extern only fails when the tactic
# first calls it, so resolve the path up front and fail before measuring.
cvc5_dynlib=""
if [[ "$runs_smt_lane" == "true" ]]; then
  for candidate in \
      "$hammer_repo/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib" \
      "$hammer_repo/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"; do
    if [[ -f "$candidate" ]]; then
      cvc5_dynlib="$candidate"
      break
    fi
  done
  if [[ -z "$cvc5_dynlib" ]]; then
    printf 'error: the smt-only lane needs the precompiled lean-cvc5 library, not found under %s\n' \
      "$hammer_repo/.lake/packages/cvc5/.lake/build/lib" >&2
    exit 1
  fi
fi

write_duper_case() {
  local source="$1"
  local output="$2"

  {
    printf 'import Duper\n\n'
    cat <<'EOF'
open Lean Elab Tactic

private def runBenchmarkDuper (premises : TSyntaxArray `term) : TacticM Unit := do
  let tactic ← `(tactic| duper [*, $premises,*])
  let start ← IO.monoMsNow
  try
    evalTactic tactic
    logInfo m!"BENCHMARK_MS={(← IO.monoMsNow) - start}"
  catch e =>
    logInfo m!"BENCHMARK_MS={(← IO.monoMsNow) - start}"
    throw e

syntax "benchmark_hammer" : tactic
syntax "benchmark_hammer" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| benchmark_hammer) => runBenchmarkDuper #[]
  | `(tactic| benchmark_hammer [$premises,*]) =>
    runBenchmarkDuper premises

EOF
    tail -n +2 "$source"
  } > "$output"
}

write_direct_case() {
  local source="$1"
  local output="$2"
  local profile="$3"
  local trust reconstruct

  if [[ "$profile" == "grind-only" ]]; then
    {
      printf 'import Hammer\n\n'
      cat <<'EOF'
open Lean Elab Tactic

private def runBenchmarkDirect (premises : TSyntaxArray `term) : TacticM Unit := do
  let params : TSyntaxArray `Lean.Parser.Tactic.grindParam ← premises.mapM fun premise => do
    let premise : TSyntax `term := ⟨premise⟩
    `(Lean.Parser.Tactic.grindParam| $(premise):term)
  let tactic ← `(tactic| grind [$params,*])
  let start ← IO.monoMsNow
  try
    evalTactic tactic
    logInfo m!"BENCHMARK_MS={(← IO.monoMsNow) - start}"
  catch e =>
    logInfo m!"BENCHMARK_MS={(← IO.monoMsNow) - start}"
    throw e

syntax "benchmark_hammer" : tactic
syntax "benchmark_hammer" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| benchmark_hammer) => runBenchmarkDirect #[]
  | `(tactic| benchmark_hammer [$premises,*]) =>
    runBenchmarkDirect premises

EOF
      tail -n +2 "$source"
    } > "$output"
    return
  fi

  case "$profile" in
    crush-verify)
      trust="trust"
      reconstruct="auto"
      ;;
    crush-core)
      trust="reconstruct"
      reconstruct="core"
      ;;
    crush-alethe)
      trust="reconstruct"
      reconstruct="alethe"
      ;;
    crush-portfolio)
      trust="reconstruct"
      reconstruct="auto"
      ;;
    *)
      printf 'error: unsupported direct LeanHammer profile: %s\n' "$profile" >&2
      return 1
      ;;
  esac

  {
    printf 'import Hammer\n\n'
    cat <<EOF
open Lean Elab Tactic

private def runBenchmarkDirect (premises : TSyntaxArray \`term) : TacticM Unit :=
    withMainContext do
  let terms ← premises.mapM fun premise => do
    let proof ← Term.elabTerm premise none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let descr := premise.reprint.getD "benchmark hint"
    pure (proof, descr)
  let cfg := {
    Crush.Config.ofOptions (← getOptions) with
    backend := .$solver
    timeout := $timeout
    trust := .$trust
    reconstruct := .$reconstruct
    profile := $crush_profile
    profileMachine := true
  }
  let start <- IO.monoMsNow
  try
    Crush.runCrush (← getMainGoal) cfg {
      terms
      allHyps := true
      allowPremiseSelection := false
    }
    let stop <- IO.monoMsNow
    logInfo m!"BENCHMARK_MS={stop - start}"
  catch e =>
    let stop <- IO.monoMsNow
    logInfo m!"BENCHMARK_MS={stop - start}"
    throw e

syntax "benchmark_hammer" : tactic
syntax "benchmark_hammer" "[" term,* "]" : tactic

elab_rules : tactic
  | \`(tactic| benchmark_hammer) => runBenchmarkDirect #[]
  | \`(tactic| benchmark_hammer [\$premises,*]) =>
    runBenchmarkDirect premises

EOF
    tail -n +2 "$source"
  } > "$output"
}

smt_config="(timeout := $smt_timeout)"
if [[ "$smt_mono" == "true" ]]; then
  smt_config="+mono $smt_config"
fi

# lean-smt reconstructs cvc5's Alethe certificate in Lean. It reports an
# unhandled Alethe rule by leaving that step as an open goal instead of
# failing, so the generated lane must check the goal list itself and emit its
# own machine record. The record uses the same field layout and reconstruction
# vocabulary as `CRUSH_PROFILE` so both tools normalize into one report.
write_smt_case() {
  local source="$1"
  local output="$2"

  {
    printf 'import Smt\n\n'
    cat <<EOF
open Lean Elab Tactic Meta

private def smtBenchSanitize (value : String) : String :=
  value.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

private def smtBenchRecord (decl : String) (goalHash : UInt64)
    (outcome replay detail : String) (nanos : Nat) : String :=
  s!"SMT_PROFILE\t1\t{smtBenchSanitize decl}\t{goalHash}\t{outcome}\t\
{replay}\t{smtBenchSanitize detail}\t{nanos}\t\t"

private def smtBenchContains (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

/-- Classify a lean-smt diagnostic with the shared reconstruction vocabulary. -/
private def smtBenchOutcome (message : String) : String × String :=
  let text := message.toLower
  if smtBenchContains text "either it is false" ||
      smtBenchContains text "could not produce a counter-example" then
    ("sat", "-")
  else if smtBenchContains text "try providing more hints" ||
      smtBenchContains text "solver returned unknown" then
    ("unknown", "-")
  else if smtBenchContains text "failed to reconstruct proof for unsat result" then
    ("reconstruction-failed", "no-certificate")
  else if smtBenchContains text "failed to reconstruct sort" ||
      smtBenchContains text "failed to reconstruct term" ||
      smtBenchContains text "expected a sort, but got" then
    ("reconstruction-failed", "term-gap")
  -- lean-smt's own translators report the first two. The rest are cvc5
  -- rejecting a query lean-smt had already built, which is still an encoding
  -- limit and not a replay one: no proof existed to replay. Observed on this
  -- workload as a higher-order arrow reaching the parser, a variable-width
  -- bitvector, and an empty datatype declaration.
  else if smtBenchContains text "no translator matched" ||
      smtBenchContains text "cannot translate" ||
      smtBenchContains text "not declared as a type" ||
      smtBenchContains text "has variable width" ||
      smtBenchContains text "invalid datatype declaration" then
    ("translation-failed", "-")
  else if smtBenchContains text "unexpected check-sat result" then
    ("reconstruction-failed", "certificate-error")
  else if smtBenchContains text "maximum number of heartbeats" ||
      smtBenchContains text "deterministic) timeout" ||
      smtBenchContains text "timed out" then
    ("timeout", "-")
  -- Any other error raised through the cvc5 API. Kept distinct so it is not
  -- silently attributed to certificate replay.
  else if smtBenchContains text "cvc5.error" then
    ("solver-error", "-")
  else
    ("reconstruction-failed", "replay-exception")

private def runBenchmarkSmt (premises : TSyntaxArray \`term) : TacticM Unit :=
    withMainContext do
  -- \`[*]\` already contributes every local hypothesis. Naming one again as a
  -- hint makes Auto's monomorphization reject the whole query with "does not
  -- accept duplicated input terms", so drop hints that only name a
  -- hypothesis. LeanHammer's own smt pipeline filters its suggestions the
  -- same way. Hints naming global lemmas are kept.
  let lctx <- getLCtx
  let hints : Array (TSyntax \`Smt.Tactic.smtHintElem) <-
    premises.filterMapM fun premise => do
      if premise.raw.isIdent &&
          (lctx.findFromUserName? premise.raw.getId).isSome then
        return none
      return some (<- \`(Smt.Tactic.smtHintElem| \$premise:term))
  let decl := toString ((<- Term.getDeclName?).getD \`anonymous)
  let goalText := (toString (<- ppExpr (<- (<- getMainGoal).getType)))
    |>.replace "\t" " "
    |>.replace "\n" " "
  let goalHash := hash goalText
  let start <- IO.monoNanosNow
  -- CoreM's ordinary \`try\` rethrows heartbeat exhaustion without running the
  -- handler, which would drop this VC's record entirely.
  let failure? <- tryCatchRuntimeEx
    (do
      evalTactic (<- \`(tactic| smt $smt_config [*, \$hints,*]))
      pure none)
    (fun ex => pure (some ex))
  let nanos := (<- IO.monoNanosNow) - start
  logInfo m!"BENCHMARK_MS={nanos / 1000000}"
  match failure? with
  | none =>
    let remaining <- getUnsolvedGoals
    if remaining.isEmpty then
      IO.println (smtBenchRecord decl goalHash "alethe-reconstructed" "-" "-" nanos)
    else
      IO.println (smtBenchRecord decl goalHash "reconstruction-failed" "rule-gap"
        s!"{remaining.length} replayed step(s) left as open goals" nanos)
      throwError "lean-smt did not close the goal: \
{remaining.length} open goal(s) remain after proof replay"
  | some ex =>
    let message <- ex.toMessageData.toString
    let (outcome, replay) := smtBenchOutcome message
    IO.println (smtBenchRecord decl goalHash outcome replay message nanos)
    throw ex

syntax "benchmark_hammer" : tactic
syntax "benchmark_hammer" "[" term,* "]" : tactic

elab_rules : tactic
  | \`(tactic| benchmark_hammer) => runBenchmarkSmt #[]
  | \`(tactic| benchmark_hammer [\$premises,*]) =>
    runBenchmarkSmt premises

EOF
    tail -n +2 "$source"
  } > "$output"
}

# Profiles whose Lean source the harness generates itself. They import the
# backend directly and must not receive `-Dbenchmark.profile`, which only
# exists in LeanHammer's own `Benchmark.Harness` module.
is_generated_profile() {
  case "$1" in
    duper-only|grind-only|smt-only|\
crush-verify|crush-core|crush-alethe|crush-portfolio) return 0 ;;
    *) return 1 ;;
  esac
}

classify_failure_log() {
  awk '
    {
      line = tolower($0)
      if (line ~ /timed out|timeout at|deterministic\) timeout|solver exited without a verdict|heartbeat|maxsaturation|saturation time|saturation limit/)
        timeout = 1
      if (line ~ /translation|unsupported|higher-order|cannot translate|cannot encode/)
        translation = 1
    }
    END {
      if (timeout) print "timeout"
      else if (translation) print "translation"
      else print "tactic"
    }
  ' "$1"
}

failure_message() {
  awk '
    {
      line = tolower($0)
      if (diagnostic == "" &&
          line ~ /timed out|timeout at|deterministic\) timeout|solver exited without a verdict|heartbeat|maxsaturation|saturation time|saturation limit|translation|unsupported|higher-order|cannot translate|cannot encode/)
        diagnostic = $0
      if (fallback == "" && line ~ /error:/) fallback = $0
    }
    END {
      if (diagnostic != "") message = diagnostic
      else if (fallback != "") message = fallback
      else message = "-"
      gsub(/\t/, " ", message)
      print message
    }
  ' "$1"
}

case "$resume" in
  true|false) ;;
  *) printf 'error: RESUME must be true or false\n' >&2; exit 1 ;;
esac

initialize_tsv() {
  local file="$1"
  local header="$2"
  if [[ "$resume" != "true" || ! -f "$file" ]]; then
    printf '%b\n' "$header" > "$file"
  fi
}

initialize_tsv "$results" 'profile\tcase\trun\tstatus\ttactic_ms'
initialize_tsv "$measurements" 'suite\tlane\trepeat\tvc_key\tstatus\tcategory\tmilliseconds\tmessage'
initialize_tsv "$profiles_out" 'suite\tlane\trepeat\tvc_key\tdeclaration\tgoal_hash\toutcome\treplay\tdetail\ttotal_nanos\tphases\tmetrics'
initialize_tsv "$metadata" 'hammer_commit\ttoolchain\tduper_commit\tduper_timeout\tsolver\ttimeout\tmax_heartbeats\tmax_rec_depth\tcrush_profile\tcrush_commit\tcrush_dirty\tcrush_root\tsmt_commit\tsmt_timeout\tsmt_mono'

legacy_checkpoints=false
if [[ "$resume" == "true" && ! -f "$checkpoints" ]]; then
  legacy_checkpoints=true
fi
initialize_tsv "$checkpoints" 'profile\tcase\trun'
if [[ "$legacy_checkpoints" == "true" ]]; then
  while IFS=$'\t' read -r profile case_name run _; do
    [[ "$profile" != "profile" ]] || continue
    if [[ "$case_name" == "00_import_only" ]] ||
        awk -F '\t' -v profile="$profile" -v case_name="$case_name" -v run="$run" '
          NR > 1 && $2 == profile && $3 == run && $4 == case_name { found = 1 }
          END { exit !found }
        ' "$measurements"; then
      printf '%s\t%s\t%s\n' "$profile" "$case_name" "$run" >> "$checkpoints"
    fi
  done < "$results"
fi

crush_dirty=false
if [[ -n "$(git -C "$crush_root" status --porcelain -- \
    . ':(exclude)BenchmarkResults')" ]]; then
  crush_dirty=true
fi
duper_commit="$(git -C "$hammer_repo/.lake/packages/Duper" rev-parse HEAD)"
smt_commit="-"
if [[ -d "$hammer_repo/.lake/packages/Smt" ]]; then
  smt_commit="$(git -C "$hammer_repo/.lake/packages/Smt" rev-parse HEAD)"
fi
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$(git -C "$hammer_repo" rev-parse HEAD)" \
  "$(tr -d '\r\n' < "$hammer_repo/lean-toolchain")" \
  "$duper_commit" \
  "$duper_timeout" \
  "$solver" \
  "$timeout" \
  "$max_heartbeats" \
  "$max_rec_depth" \
  "$crush_profile" \
  "$(git -C "$crush_root" rev-parse HEAD)" \
  "$crush_dirty" \
  "$crush_root" \
  "$smt_commit" \
  "$smt_timeout" \
  "$smt_mono" >> "$metadata"

checkpoint_complete() {
  local profile="$1"
  local case_name="$2"
  local run="$3"
  [[ "$resume" == "true" ]] || return 1
  awk -F '\t' -v profile="$profile" -v case_name="$case_name" -v run="$run" '
    NR > 1 && $1 == profile && $2 == case_name && $3 == run { found = 1 }
    END { exit !found }
  ' "$checkpoints"
}

remove_checkpoint_rows() {
  local profile="$1"
  local case_name="$2"
  local run="$3"
  local temporary="$out_dir/.resume.$$.tsv"
  awk -F '\t' -v OFS='\t' -v profile="$profile" -v case_name="$case_name" \
    -v run="$run" \
    'NR == 1 || !($1 == profile && $2 == case_name && $3 == run)' \
    "$results" > "$temporary" && mv "$temporary" "$results"
  awk -F '\t' -v OFS='\t' -v profile="$profile" -v case_name="$case_name" \
    -v run="$run" \
    'NR == 1 || !($2 == profile && $3 == run && $4 == case_name)' \
    "$measurements" > "$temporary" && mv "$temporary" "$measurements"
  awk -F '\t' -v OFS='\t' -v profile="$profile" -v case_name="$case_name" \
    -v run="$run" \
    'NR == 1 || !($2 == profile && $3 == run && $4 == case_name)' \
    "$profiles_out" > "$temporary" && mv "$temporary" "$profiles_out"
  awk -F '\t' -v OFS='\t' -v profile="$profile" -v case_name="$case_name" \
    -v run="$run" \
    'NR == 1 || !($1 == profile && $2 == case_name && $3 == run)' \
    "$checkpoints" > "$temporary" && mv "$temporary" "$checkpoints"
}

case_files=("$hammer_repo"/Benchmark/Cases/*.lean)
if [[ -n "${HAMMER_CASES:-}" ]]; then
  case_files=()
  read -r -a selected_cases <<< "$HAMMER_CASES"
  for selected in "${selected_cases[@]}"; do
    if [[ "$selected" == *.lean ]]; then
      case_files+=("$hammer_repo/Benchmark/Cases/$selected")
    else
      case_files+=("$hammer_repo/Benchmark/Cases/$selected.lean")
    fi
  done
fi

for profile in "${profiles[@]}"; do
  harness_profile="$profile"
  case "$profile" in
    auto-duper) harness_profile="auto-only" ;;
    aesop-auto-duper) harness_profile="aesop-auto" ;;
  esac
  profile_marker="CRUSH_PROFILE"
  if [[ "$profile" == "smt-only" ]]; then
    profile_marker="SMT_PROFILE"
  fi
  for case_file in "${case_files[@]}"; do
    case_name="$(basename "$case_file" .lean)"
    relative_case="Benchmark/Cases/$(basename "$case_file")"
    input_case="$relative_case"
    if [[ "$profile" == "duper-only" ]]; then
      generated="$out_dir/generated/$profile/$(basename "$case_file")"
      mkdir -p "$(dirname "$generated")"
      write_duper_case "$case_file" "$generated"
      input_case="$generated"
    elif [[ "$profile" == "smt-only" ]]; then
      generated="$out_dir/generated/$profile/$(basename "$case_file")"
      mkdir -p "$(dirname "$generated")"
      write_smt_case "$case_file" "$generated"
      input_case="$generated"
    elif [[ "$profile" == "crush-verify" || "$profile" == "crush-core" ||
        "$profile" == "crush-alethe" || "$profile" == "crush-portfolio" ||
        "$profile" == "grind-only" ]]; then
      generated="$out_dir/generated/$profile/$(basename "$case_file")"
      mkdir -p "$(dirname "$generated")"
      write_direct_case "$case_file" "$generated" "$profile"
      input_case="$generated"
    fi
    for ((run = 1; run <= repeats; run++)); do
      if checkpoint_complete "$profile" "$case_name" "$run"; then
        printf 'checkpoint: skipping %-12s %-24s run %s\n' \
          "$profile" "$case_name" "$run"
        continue
      fi
      if [[ "$resume" == "true" ]]; then
        remove_checkpoint_rows "$profile" "$case_name" "$run"
      fi
      log="$logs/${profile}-${case_name}-${run}.log"
      lean_args=(
        "-DElab.async=false"
        "-DmaxHeartbeats=$max_heartbeats"
        "-DmaxRecDepth=$max_rec_depth"
      )
      # Only lanes that can reach Duper register its options. The lean-smt
      # lane imports `Smt` alone, and Lean rejects a `-D` for an option no
      # imported module declares. Keep this strict rather than using
      # `-Dweak.`, so a renamed option fails loudly instead of silently
      # letting a Duper lane saturate without a bound.
      if [[ "$profile" != "smt-only" ]]; then
        lean_args+=("-Dduper.maxSaturationTime=$duper_timeout")
      else
        lean_args+=("--load-dynlib=$cvc5_dynlib")
      fi
      if [[ "$profile" == crush-* || "$profile" == "crush-only" ||
          "$profile" == "aesop-crush" ]]; then
        lean_args+=(
          "-Dcrush.profile=$crush_profile"
          "-Dcrush.profile.machine=true"
        )
      fi
      if ! is_generated_profile "$profile"; then
        lean_args+=("-Dbenchmark.profile=$harness_profile")
      fi
      if "$script_dir/with-local-crush.sh" "$hammer_repo" \
          "${lean_args[@]}" "$input_case" > "$log" 2>&1; then
        status=pass
      else
        status=fail
      fi
      if grep -q "invalid -D parameter" "$log"; then
        grep -m 1 -A 2 "invalid -D parameter" "$log" >&2
        printf 'error: %s rejected a Lean option; see %s\n' "$profile" "$log" >&2
        exit 1
      fi
      tactic_ms="$(sed -n 's/.*BENCHMARK_MS=\([0-9][0-9]*\).*/\1/p' "$log" | tail -n 1)"
      tactic_ms="${tactic_ms:-0}"
      printf '%s\t%s\t%s\t%s\t%s\n' \
        "$profile" "$case_name" "$run" "$status" "$tactic_ms" >> "$results"
      if [[ "$case_name" != "00_import_only" ]]; then
        category="-"
        message="-"
        if [[ "$status" != "pass" ]]; then
          profile_category="$(awk -F '\t' -v tag="$profile_marker" '
            {
              marker = index($0, tag "\t")
              if (marker == 0) next
              split(substr($0, marker), row, "\t")
              category = row[5]
            }
            END {
              if (category == "") print "tactic"
              else print category
            }
          ' "$log")"
          category="$(classify_failure_log "$log")"
          if [[ "$category" == "tactic" && "$profile_category" != "tactic" ]]; then
            category="$profile_category"
          fi
          message="$(failure_message "$log")"
        fi
        printf 'leanhammer\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
          "$profile" "$run" "$case_name" "$status" "$category" "$tactic_ms" \
          "$message" >> "$measurements"
        awk -v lane="$profile" -v repeat="$run" -v vc="$case_name" \
            -v profiles="$profiles_out" -v tag="$profile_marker" '
          BEGIN { FS = OFS = "\t" }
          {
            marker = index($0, tag "\t")
            if (marker == 0) next
            split(substr($0, marker), row, "\t")
            print "leanhammer", lane, repeat, vc, row[3], row[4], row[5],
                  row[6], row[7], row[8], row[9], row[10] >> profiles
          }
        ' "$log"
      fi
      printf '%s\t%s\t%s\n' "$profile" "$case_name" "$run" >> "$checkpoints"
      printf '%-12s %-24s run %s: %-4s %6sms\n' \
        "$profile" "$case_name" "$run" "$status" "$tactic_ms"
    done
  done
done

awk -F '\t' '
  BEGIN {
    OFS = "\t"
    print "profile", "attempted", "passed", "failed", "pass_pct",
          "total_ms", "mean_ms", "min_ms", "max_ms"
  }
  NR > 1 && $2 != "00_import_only" {
    profile = $1
    seen[profile] = 1
    attempted[profile]++
    total[profile] += $5
    if (!(profile in minimum) || $5 < minimum[profile]) minimum[profile] = $5
    if (!(profile in maximum) || $5 > maximum[profile]) maximum[profile] = $5
    if ($4 == "pass") passed[profile]++
  }
  END {
    for (profile in seen) {
      failed = attempted[profile] - passed[profile]
      pct = attempted[profile] ? 100 * passed[profile] / attempted[profile] : 0
      printf "%s\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%.1f\t%.1f\n",
        profile, attempted[profile], passed[profile], failed, pct,
        total[profile], total[profile] / attempted[profile],
        minimum[profile], maximum[profile]
    }
  }
' "$results" > "$summary"

printf '\nSummary (excluding import-only case):\n'
awk -F '\t' -v repeats="$repeats" '
  function reportPair(label, left, right,    c, lk, rk, common, leftTotal, rightTotal) {
    if (!(left in profiles) || !(right in profiles)) return
    for (c in caseNames) {
      lk = left SUBSEP c
      rk = right SUBSEP c
      if (passed[lk] == repeats && passed[rk] == repeats) {
        common += 1
        leftTotal += caseTotal[lk] / caseRuns[lk]
        rightTotal += caseTotal[rk] / caseRuns[rk]
      }
    }
    printf "%-12s %2d common successes, %.1fms %s, %.1fms %s\n",
      label, common, common ? leftTotal / common : 0, left,
      common ? rightTotal / common : 0, right
  }
  NR > 1 && $2 != "00_import_only" {
    key = $1 SUBSEP $2
    profiles[$1] = 1
    cases[key] = 1
    caseNames[$2] = 1
    caseTotal[key] += $5
    caseRuns[key] += 1
    if ($4 == "pass") {
      passed[key] += 1
      successTotal[$1] += $5
      successRuns[$1] += 1
    }
  }
  END {
    for (profile in profiles) {
      solved = 0
      count = 0
      for (key in cases) {
        split(key, parts, SUBSEP)
        if (parts[1] == profile) {
          count += 1
          if (passed[key] == repeats) solved += 1
        }
      }
      printf "%-12s %2d/%2d solved, %.1fms successful-run mean\n",
        profile, solved, count,
        successRuns[profile] ? successTotal[profile] / successRuns[profile] : 0
    }
    print ""
    reportPair("auto-duper", "auto-duper", "crush-only")
    reportPair("duper", "duper-only", "crush-only")
    reportPair("with-aesop", "aesop-auto-duper", "aesop-crush")
    reportPair("direct-old", "auto-only", "crush-only")
    reportPair("aesop-old", "aesop-auto", "aesop-crush")
    reportPair("grind", "grind-only", "crush-portfolio")
    reportPair("core", "crush-core", "crush-portfolio")
    reportPair("alethe", "crush-alethe", "crush-portfolio")
    reportPair("lean-smt", "smt-only", "crush-portfolio")
    reportPair("smt-alethe", "smt-only", "crush-alethe")
  }
' "$results"

if ! python3 "$script_dir/benchmark-report.py" \
    --measurements "$measurements" --profiles "$profiles_out" \
    --out-dir "$out_dir" --require-uniform-headline; then
  printf 'error: failed to generate measurement reports\n' >&2
  exit 1
fi

printf '\nAll-VC headline summary:\n'
column -t -s $'\t' "$out_dir/headline-summary.tsv" 2>/dev/null ||
  cat "$out_dir/headline-summary.tsv"
printf '\nMatched-VC comparison:\n'
column -t -s $'\t' "$out_dir/comparison.tsv" 2>/dev/null ||
  cat "$out_dir/comparison.tsv"
printf '\nReconstruction coverage:\n'
column -t -s $'\t' "$out_dir/reconstruction-summary.tsv" 2>/dev/null ||
  cat "$out_dir/reconstruction-summary.tsv"
printf '\nReconstruction failures:\n'
column -t -s $'\t' "$out_dir/reconstruction-failures.tsv" 2>/dev/null ||
  cat "$out_dir/reconstruction-failures.tsv"
printf '\nAlethe replay scaling:\n'
column -t -s $'\t' "$out_dir/alethe-replay-scaling-summary.tsv" 2>/dev/null ||
  cat "$out_dir/alethe-replay-scaling-summary.tsv"
printf '\nResults: %s\n' "$out_dir"

missing_headline="$(
  awk -F '\t' 'NR > 1 { missing += $8 } END { print missing + 0 }' \
    "$out_dir/headline-summary.tsv"
)"
if [[ "$missing_headline" -gt 0 ]]; then
  printf 'error: %s headline VC attempt(s) are missing\n' \
    "$missing_headline" >&2
  exit 1
fi
