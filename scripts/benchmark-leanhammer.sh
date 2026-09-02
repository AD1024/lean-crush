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
max_heartbeats="${MAX_HEARTBEATS:-1000000}"
max_rec_depth="${MAX_RECURSION_DEPTH:-1000000}"
crush_profile="${CRUSH_PROFILE:-true}"
use_mathlib_cache="${USE_MATHLIB_CACHE:-true}"
out_dir="${OUT_DIR:-$crush_root/BenchmarkResults/leanhammer-$(date +%Y%m%d-%H%M%S)}"
mkdir -p "$out_dir"
out_dir="$(cd "$out_dir" && pwd)"
results="$out_dir/results.tsv"
metadata="$out_dir/metadata.tsv"
summary="$out_dir/summary.tsv"
measurements="$out_dir/measurements.tsv"
profiles_out="$out_dir/profile-events.tsv"
logs="$out_dir/logs"
read -r -a profiles <<< \
  "${PROFILES:-crush-only crush-verify crush-core crush-alethe crush-portfolio grind-only duper-only auto-duper aesop-auto-duper aesop-crush}"
tmp_root=""
managed_repo=""

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

printf 'profile\tcase\trun\tstatus\ttactic_ms\n' > "$results"
printf 'suite\tlane\trepeat\tvc_key\tstatus\tcategory\tmilliseconds\tmessage\n' > "$measurements"
printf 'suite\tlane\trepeat\tvc_key\tdeclaration\tgoal_hash\toutcome\treplay\tdetail\ttotal_nanos\tphases\tmetrics\n' > "$profiles_out"
printf 'hammer_commit\ttoolchain\tduper_commit\tduper_timeout\tsolver\ttimeout\tmax_heartbeats\tmax_rec_depth\tcrush_profile\tcrush_commit\tcrush_dirty\tcrush_root\n' > "$metadata"
crush_dirty=false
if [[ -n "$(git -C "$crush_root" status --porcelain -- \
    . ':(exclude)BenchmarkResults')" ]]; then
  crush_dirty=true
fi
duper_commit="$(git -C "$hammer_repo/.lake/packages/Duper" rev-parse HEAD)"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
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
  "$crush_root" >> "$metadata"

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
  for case_file in "${case_files[@]}"; do
    case_name="$(basename "$case_file" .lean)"
    relative_case="Benchmark/Cases/$(basename "$case_file")"
    input_case="$relative_case"
    if [[ "$profile" == "duper-only" ]]; then
      generated="$out_dir/generated/$profile/$(basename "$case_file")"
      mkdir -p "$(dirname "$generated")"
      write_duper_case "$case_file" "$generated"
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
      log="$logs/${profile}-${case_name}-${run}.log"
      lean_args=(
        "-DElab.async=false"
        "-Dduper.maxSaturationTime=$duper_timeout"
        "-DmaxHeartbeats=$max_heartbeats"
        "-DmaxRecDepth=$max_rec_depth"
      )
      if [[ "$profile" == crush-* || "$profile" == "crush-only" ||
          "$profile" == "aesop-crush" ]]; then
        lean_args+=(
          "-Dcrush.profile=$crush_profile"
          "-Dcrush.profile.machine=true"
        )
      fi
      if [[ "$profile" != "duper-only" && "$profile" != "crush-verify" &&
          "$profile" != "crush-core" && "$profile" != "crush-alethe" &&
          "$profile" != "crush-portfolio" && "$profile" != "grind-only" ]]; then
        lean_args+=("-Dbenchmark.profile=$harness_profile")
      fi
      if "$script_dir/with-local-crush.sh" "$hammer_repo" \
          "${lean_args[@]}" "$input_case" > "$log" 2>&1; then
        status=pass
      else
        status=fail
      fi
      tactic_ms="$(sed -n 's/.*BENCHMARK_MS=\([0-9][0-9]*\).*/\1/p' "$log" | tail -n 1)"
      tactic_ms="${tactic_ms:-0}"
      printf '%s\t%s\t%s\t%s\t%s\n' \
        "$profile" "$case_name" "$run" "$status" "$tactic_ms" >> "$results"
      if [[ "$case_name" != "00_import_only" ]]; then
        category="-"
        message="-"
        if [[ "$status" != "pass" ]]; then
          profile_category="$(awk -F '\t' '
            /CRUSH_PROFILE\t/ {
              marker = index($0, "CRUSH_PROFILE\t")
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
            -v profiles="$profiles_out" '
          BEGIN { FS = OFS = "\t" }
          {
            marker = index($0, "CRUSH_PROFILE\t")
            if (marker == 0) next
            split(substr($0, marker), row, "\t")
            print "leanhammer", lane, repeat, vc, row[3], row[4], row[5],
                  row[6], row[7], row[8], row[9], row[10] >> profiles
          }
        ' "$log"
      fi
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
