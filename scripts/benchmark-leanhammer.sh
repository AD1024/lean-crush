#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
crush_root="$(cd "$script_dir/.." && pwd)"
hammer_repo="${HAMMER_REPO:-$crush_root/../LeanHammer}"
repeats="${REPEATS:-1}"
out_dir="${OUT_DIR:-$crush_root/BenchmarkResults/leanhammer-$(date +%Y%m%d-%H%M%S)}"
results="$out_dir/results.tsv"
metadata="$out_dir/metadata.tsv"
logs="$out_dir/logs"
profiles=(auto-only crush-only aesop-auto aesop-crush)

if [[ ! -d "$hammer_repo/Benchmark/Cases" ]]; then
  printf 'error: LeanHammer benchmark not found at %s\n' "$hammer_repo" >&2
  exit 1
fi

if [[ ! -f "$crush_root/.lake/build/lib/lean/Crush.olean" ]]; then
  printf 'error: local Crush is not built; run `lake build Crush`\n' >&2
  exit 1
fi

mkdir -p "$logs"
printf 'profile\tcase\trun\tstatus\ttactic_ms\n' > "$results"
printf 'hammer_commit\ttoolchain\tcrush_commit\tcrush_dirty\tcrush_root\n' > "$metadata"
crush_dirty=false
if [[ -n "$(git -C "$crush_root" status --porcelain)" ]]; then
  crush_dirty=true
fi
printf '%s\t%s\t%s\t%s\t%s\n' \
  "$(git -C "$hammer_repo" rev-parse HEAD)" \
  "$(tr -d '\r\n' < "$hammer_repo/lean-toolchain")" \
  "$(git -C "$crush_root" rev-parse HEAD)" \
  "$crush_dirty" \
  "$crush_root" >> "$metadata"

for profile in "${profiles[@]}"; do
  for case_file in "$hammer_repo"/Benchmark/Cases/*.lean; do
    case_name="$(basename "$case_file" .lean)"
    relative_case="Benchmark/Cases/$(basename "$case_file")"
    for ((run = 1; run <= repeats; run++)); do
      log="$logs/${profile}-${case_name}-${run}.log"
      if "$script_dir/with-local-crush.sh" "$hammer_repo" \
          "-Dbenchmark.profile=$profile" "$relative_case" > "$log" 2>&1; then
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

printf '\nSummary (excluding import-only case):\n'
awk -F '\t' -v repeats="$repeats" '
  function reportPair(label, left, right,    c, lk, rk, common, leftTotal, rightTotal) {
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
    reportPair("direct", "auto-only", "crush-only")
    reportPair("with-aesop", "aesop-auto", "aesop-crush")
  }
' "$results"

printf '\nResults: %s\n' "$out_dir"
