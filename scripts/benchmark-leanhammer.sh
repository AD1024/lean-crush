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
out_dir="${OUT_DIR:-$crush_root/BenchmarkResults/leanhammer-$(date +%Y%m%d-%H%M%S)}"
results="$out_dir/results.tsv"
metadata="$out_dir/metadata.tsv"
summary="$out_dir/summary.tsv"
logs="$out_dir/logs"
read -r -a profiles <<< \
  "${PROFILES:-duper-only auto-duper crush-only aesop-auto-duper aesop-crush}"
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

printf 'profile\tcase\trun\tstatus\ttactic_ms\n' > "$results"
printf 'hammer_commit\ttoolchain\tduper_commit\tduper_timeout\tcrush_commit\tcrush_dirty\tcrush_root\n' > "$metadata"
crush_dirty=false
if [[ -n "$(git -C "$crush_root" status --porcelain -- \
    . ':(exclude)BenchmarkResults')" ]]; then
  crush_dirty=true
fi
duper_commit="$(git -C "$hammer_repo/.lake/packages/Duper" rev-parse HEAD)"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$(git -C "$hammer_repo" rev-parse HEAD)" \
  "$(tr -d '\r\n' < "$hammer_repo/lean-toolchain")" \
  "$duper_commit" \
  "$duper_timeout" \
  "$(git -C "$crush_root" rev-parse HEAD)" \
  "$crush_dirty" \
  "$crush_root" >> "$metadata"

for profile in "${profiles[@]}"; do
  harness_profile="$profile"
  case "$profile" in
    auto-duper) harness_profile="auto-only" ;;
    aesop-auto-duper) harness_profile="aesop-auto" ;;
  esac
  for case_file in "$hammer_repo"/Benchmark/Cases/*.lean; do
    case_name="$(basename "$case_file" .lean)"
    relative_case="Benchmark/Cases/$(basename "$case_file")"
    input_case="$relative_case"
    if [[ "$profile" == "duper-only" ]]; then
      generated="$out_dir/generated/duper-only/$(basename "$case_file")"
      mkdir -p "$(dirname "$generated")"
      write_duper_case "$case_file" "$generated"
      input_case="$generated"
    fi
    for ((run = 1; run <= repeats; run++)); do
      log="$logs/${profile}-${case_name}-${run}.log"
      lean_args=("-Dduper.maxSaturationTime=$duper_timeout")
      if [[ "$profile" != "duper-only" ]]; then
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
      label, common, leftTotal / common, left, rightTotal / common, right
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
        profile, solved, count, successTotal[profile] / successRuns[profile]
    }
    print ""
    reportPair("auto-duper", "auto-duper", "crush-only")
    reportPair("duper", "duper-only", "crush-only")
    reportPair("with-aesop", "aesop-auto-duper", "aesop-crush")
    reportPair("direct-old", "auto-only", "crush-only")
    reportPair("aesop-old", "aesop-auto", "aesop-crush")
  }
' "$results"

printf '\nResults: %s\n' "$out_dir"
