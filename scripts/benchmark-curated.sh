#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
crush_root="$(cd "$script_dir/.." && pwd)"
source "$script_dir/benchmark-common.sh"

curated_repo="${CURATED_REPO:-}"
curated_url="${CURATED_REPO_URL:-git@github.com:AD1024/Lean-SMT-Benchmarks.git}"
# Each backend is a branch, so a revision here is a branch tip rather than one
# commit the whole suite shares. Pin per branch instead.
curated_ref_main="${CURATED_REF_MAIN:-main}"
curated_ref_auto="${CURATED_REF_AUTO:-auto}"
curated_ref_duper="${CURATED_REF_DUPER:-duper}"
curated_ref_crush="${CURATED_REF_CRUSH:-crush}"
curated_ref_smt="${CURATED_REF_SMT:-lean-smt}"
# Every branch needs its own Lake build, so keeping the trees between runs is
# the difference between seconds and minutes of rebuilding.
curated_trees="${CURATED_TREES:-$crush_root/BenchmarkResults/curated-trees}"
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
out_dir="${OUT_DIR:-$crush_root/BenchmarkResults/curated-$(date +%Y%m%d-%H%M%S)}"
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
  "${PROFILES:-crush-verify crush-core crush-alethe crush-portfolio smt-only grind-only duper-only auto-smt}"
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
# The lean-smt branch writes its solver configuration into its own harness,
# because lean-smt takes it as tactic syntax rather than as an option. Refuse a
# request this harness cannot honour rather than recording a number under a
# configuration that was never applied.
if [[ "$runs_smt_lane" == "true" ]] &&
    [[ "$smt_timeout" != "5" || "$smt_mono" != "true" ]]; then
  printf 'error: the lean-smt branch fixes its configuration at +mono (timeout := 5); got SMT_TIMEOUT=%s SMT_MONO=%s\n' \
    "$smt_timeout" "$smt_mono" >&2
  printf '       change it on the branch, not here\n' >&2
  exit 1
fi

# The branch trees survive the run on purpose: each carries its own Lake build,
# and rebuilding five of them costs minutes. CURATED_TREES says where they live.
trap 'exit 130' INT
trap 'exit 143' TERM

# Which branch each lane is measured on. The suite keeps one backend per
# branch so that no backend's dependencies reach another's environment, which
# is what makes the lanes comparable. Crush's four lanes differ only in
# options, so they share a branch.
profile_branch() {
  case "$1" in
    crush-verify|crush-core|crush-alethe|crush-portfolio) printf 'crush' ;;
    duper-only) printf 'duper' ;;
    auto-smt) printf 'auto' ;;
    smt-only) printf 'lean-smt' ;;
    grind-only) printf 'main' ;;
    *) return 1 ;;
  esac
}

branch_ref() {
  case "$1" in
    main) printf '%s' "$curated_ref_main" ;;
    auto) printf '%s' "$curated_ref_auto" ;;
    duper) printf '%s' "$curated_ref_duper" ;;
    crush) printf '%s' "$curated_ref_crush" ;;
    lean-smt) printf '%s' "$curated_ref_smt" ;;
    *) return 1 ;;
  esac
}

needed_branches=()
for candidate in "${profiles[@]}"; do
  branch="$(profile_branch "$candidate")" || {
    printf 'error: unsupported profile: %s\n' "$candidate" >&2
    exit 1
  }
  seen=false
  for existing in ${needed_branches[@]+"${needed_branches[@]}"}; do
    if [[ "$existing" == "$branch" ]]; then
      seen=true
    fi
  done
  if [[ "$seen" != "true" ]]; then
    needed_branches+=("$branch")
  fi
done

if [[ -z "$curated_repo" ]]; then
  managed_repo="$(benchmark_ensure_repo "Curated" "$curated_url" \
    "$(branch_ref "${needed_branches[0]}")" "$source_cache/Curated")"
else
  # A local checkout still has to yield one tree per branch, so treat it as the
  # repository to add worktrees from rather than as a tree to measure in.
  managed_repo="$(cd "$curated_repo" && pwd)"
fi

mkdir -p "$logs"
printf 'Building local Crush\n'
if ! (cd "$crush_root" && lake build Crush) \
    > "$out_dir/build-crush.log" 2>&1; then
  tail -n 80 "$out_dir/build-crush.log" >&2
  printf 'error: local Crush build failed\n' >&2
  exit 1
fi

mkdir -p "$curated_trees"
curated_trees="$(cd "$curated_trees" && pwd)"

# Resolved per branch below; the smt lane needs the path to lean-cvc5's
# precompiled library and the metadata rows need the dependency revisions.
cvc5_dynlib=""
duper_commit="-"
smt_commit="-"

branch_tree() {
  printf '%s/%s' "$curated_trees" "$1"
}

provision_branch() {
  local branch="$1"
  local ref tree
  ref="$(branch_ref "$branch")"
  tree="$(branch_tree "$branch")"

  if [[ -d "$tree/.git" || -f "$tree/.git" ]]; then
    git -C "$tree" fetch --quiet origin "$ref" >/dev/null 2>&1 || true
    # A tree is a build cache for one branch, never a place to edit: forcing
    # keeps a stale checkout from silently measuring something other than the
    # branch. Change the branch and let the tree follow.
    git -C "$tree" checkout --quiet --force --detach "origin/$ref" 2>/dev/null ||
      git -C "$tree" checkout --quiet --force --detach "$ref" || {
        printf 'error: could not check out %s in %s\n' "$ref" "$tree" >&2
        return 1
      }
  else
    rm -rf "$tree"
    # A branch the repository already has needs no network; one it does not is
    # fetched by name. Resolving through origin/ only when the local name is
    # absent keeps a provided local checkout usable before anything is pushed.
    local resolved="$ref"
    if ! git -C "$managed_repo" rev-parse --verify "$ref^{commit}" \
        >/dev/null 2>&1; then
      if git -C "$managed_repo" rev-parse --verify "origin/$ref^{commit}" \
          >/dev/null 2>&1; then
        resolved="origin/$ref"
      else
        git -C "$managed_repo" fetch --quiet origin "$ref" >/dev/null 2>&1 || {
          printf 'error: branch %s is not in %s\n' "$ref" "$managed_repo" >&2
          return 1
        }
        resolved="FETCH_HEAD"
      fi
    fi
    benchmark_add_worktree "$managed_repo" "$resolved" "$tree" >/dev/null ||
      return 1
  fi

  if [[ ! -d "$tree/Curated/Cases" ]]; then
    printf 'error: branch %s has no Curated/Cases\n' "$branch" >&2
    return 1
  fi

  printf 'Preparing %s branch\n' "$branch"
  if ! (cd "$tree" && lake env printenv LEAN_PATH) \
      > "$out_dir/dependencies-$branch.log" 2>&1; then
    tail -n 80 "$out_dir/dependencies-$branch.log" >&2
    printf 'error: %s dependency setup failed\n' "$branch" >&2
    return 1
  fi
  if [[ "$use_mathlib_cache" == "true" ]]; then
    benchmark_fetch_cache "$tree" "$out_dir/cache-$branch.log" || true
  fi
  # Only the Crush branch carries the package, and only it is measured against
  # the working tree rather than the pinned revision.
  if [[ "$branch" == "crush" ]]; then
    benchmark_sync_crush_sources "$crush_root" "$tree" || return 1
  fi

  printf 'Building %s branch\n' "$branch"
  if ! (cd "$tree" && lake build Curated.Harness) \
      > "$out_dir/build-branch-$branch.log" 2>&1; then
    tail -n 80 "$out_dir/build-branch-$branch.log" >&2
    printf 'error: %s build failed\n' "$branch" >&2
    return 1
  fi

  if [[ -d "$tree/.lake/packages/Duper" ]]; then
    duper_commit="$(git -C "$tree/.lake/packages/Duper" rev-parse HEAD)"
  fi
  if [[ -d "$tree/.lake/packages/Smt" ]]; then
    smt_commit="$(git -C "$tree/.lake/packages/Smt" rev-parse HEAD)"
  fi

  # lean-cvc5 sets `precompileModules`, so the `smt` tactic reaches cvc5
  # through FFI rather than by spawning a binary. A standalone `lean` process
  # does not load that library on its own, and the extern only fails when the
  # tactic first calls it, so resolve the path up front and fail before
  # measuring.
  if [[ "$branch" == "lean-smt" ]]; then
    for candidate in \
        "$tree/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib" \
        "$tree/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"; do
      if [[ -f "$candidate" ]]; then
        cvc5_dynlib="$candidate"
        break
      fi
    done
    if [[ -z "$cvc5_dynlib" ]]; then
      printf 'error: the smt-only lane needs the precompiled lean-cvc5 library, not found under %s\n' \
        "$tree/.lake/packages/cvc5/.lake/build/lib" >&2
      return 1
    fi
  fi
}

for branch in "${needed_branches[@]}"; do
  provision_branch "$branch" || exit 1
done

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
initialize_tsv "$metadata" 'curated_commit\ttoolchain\tduper_commit\tduper_timeout\tsolver\ttimeout\tmax_heartbeats\tmax_rec_depth\tcrush_profile\tcrush_commit\tcrush_dirty\tcrush_root\tsmt_commit\tsmt_timeout\tsmt_mono'

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
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$(git -C "$(branch_tree "${needed_branches[0]}")" rev-parse HEAD)" \
  "$(tr -d '\r\n' < "$(branch_tree "${needed_branches[0]}")/lean-toolchain")" \
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

# The cases are identical on every branch, so list them from the first tree
# and address them by name from whichever tree a lane runs in.
case_names=()
if [[ -n "${CURATED_CASES:-}" ]]; then
  read -r -a selected_cases <<< "$CURATED_CASES"
  for selected in "${selected_cases[@]}"; do
    case_names+=("${selected%.lean}")
  done
else
  for case_file in "$(branch_tree "${needed_branches[0]}")"/Curated/Cases/*.lean; do
    case_names+=("$(basename "$case_file" .lean)")
  done
fi

for profile in "${profiles[@]}"; do
  branch="$(profile_branch "$profile")"
  tree="$(branch_tree "$branch")"
  profile_marker="CRUSH_PROFILE"
  if [[ "$profile" == "smt-only" ]]; then
    profile_marker="SMT_PROFILE"
  fi
  # Crush's lanes are one branch differing only in options.
  crush_trust=""
  crush_reconstruct=""
  case "$profile" in
    crush-verify) crush_trust="trust"; crush_reconstruct="auto" ;;
    crush-core) crush_trust="reconstruct"; crush_reconstruct="core" ;;
    crush-alethe) crush_trust="reconstruct"; crush_reconstruct="alethe" ;;
    crush-portfolio) crush_trust="reconstruct"; crush_reconstruct="auto" ;;
  esac
  for case_name in "${case_names[@]}"; do
    input_case="Curated/Cases/$case_name.lean"
    if [[ ! -f "$tree/$input_case" ]]; then
      printf 'error: no such case on branch %s: %s\n' "$branch" "$case_name" >&2
      exit 1
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
      # Lean rejects a `-D` for an option no imported module declares, so each
      # branch only receives the options its own dependencies register. Keep
      # this strict rather than using `-Dweak.`, so a renamed option fails
      # loudly instead of silently letting a lane run unbounded.
      case "$branch" in
        duper)
          lean_args+=("-Dduper.maxSaturationTime=$duper_timeout") ;;
        lean-smt)
          lean_args+=("--load-dynlib=$cvc5_dynlib") ;;
        crush)
          lean_args+=(
            "-Dcrush.backend=$solver"
            "-Dcrush.timeout=$timeout"
            "-Dcrush.trust=$crush_trust"
            "-Dcrush.reconstruct=$crush_reconstruct"
            "-Dcrush.profile=$crush_profile"
            "-Dcrush.profile.machine=true"
          ) ;;
      esac
      if "$script_dir/with-local-crush.sh" "$tree" \
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
        printf 'curated\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
          "$profile" "$run" "$case_name" "$status" "$category" "$tactic_ms" \
          "$message" >> "$measurements"
        awk -v lane="$profile" -v repeat="$run" -v vc="$case_name" \
            -v profiles="$profiles_out" -v tag="$profile_marker" '
          BEGIN { FS = OFS = "\t" }
          {
            marker = index($0, tag "\t")
            if (marker == 0) next
            split(substr($0, marker), row, "\t")
            print "curated", lane, repeat, vc, row[3], row[4], row[5],
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
    reportPair("auto-smt", "auto-smt", "crush-portfolio")
    reportPair("duper", "duper-only", "crush-portfolio")
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
