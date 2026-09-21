#!/usr/bin/env bash

benchmark_is_git_repo() {
  git -C "$1" rev-parse --git-dir >/dev/null 2>&1
}

# A revision may be a commit, a tag, or a branch. A fresh clone keeps branches
# only as remote-tracking refs, and `rev-parse <branch>` does not consult
# `refs/remotes/origin/`, so a branch name looks unavailable unless it is tried
# as `origin/<branch>` too. Echoes the form that resolves.
benchmark_resolve_revision() {
  local destination="$1"
  local revision="$2"

  if git -C "$destination" rev-parse --verify \
      "${revision}^{commit}" >/dev/null 2>&1; then
    printf '%s\n' "$revision"
    return 0
  fi
  if git -C "$destination" rev-parse --verify \
      "origin/${revision}^{commit}" >/dev/null 2>&1; then
    printf '%s\n' "origin/${revision}"
    return 0
  fi
  return 1
}

benchmark_ensure_repo() {
  local label="$1"
  local url="$2"
  local revision="$3"
  local destination="$4"
  local existing_url

  if [[ -e "$destination" ]] && ! benchmark_is_git_repo "$destination"; then
    printf 'error: benchmark source path is not a Git repository: %s\n' \
      "$destination" >&2
    return 1
  fi

  if [[ ! -e "$destination" ]]; then
    mkdir -p "$(dirname "$destination")"
    printf 'Cloning %s at %s\n' "$label" "$revision" >&2
    git clone --filter=blob:none --no-checkout "$url" "$destination" >&2 ||
      return 1
  else
    existing_url="$(git -C "$destination" remote get-url origin 2>/dev/null || true)"
    if [[ "$existing_url" != "$url" ]]; then
      printf 'error: cached %s repository has origin %s, expected %s\n' \
        "$label" "${existing_url:-(none)}" "$url" >&2
      return 1
    fi
  fi

  if ! benchmark_resolve_revision "$destination" "$revision" >/dev/null; then
    printf 'Fetching %s revision %s\n' "$label" "$revision" >&2
    if ! git -C "$destination" fetch --filter=blob:none origin \
        "$revision" >&2; then
      git -C "$destination" fetch --filter=blob:none origin >&2 ||
        return 1
    fi
  fi

  if ! benchmark_resolve_revision "$destination" "$revision" >/dev/null; then
    printf 'error: revision %s is unavailable in %s\n' \
      "$revision" "$url" >&2
    return 1
  fi

  printf '%s\n' "$destination"
}

benchmark_add_worktree() {
  local repository="$1"
  local revision="$2"
  local destination="$3"

  git -C "$repository" worktree prune >/dev/null 2>&1 || true
  git -C "$repository" worktree add --detach "$destination" "$revision"
}

# Lake fetches each package's build outputs with `curl --retry 3` and no
# `--max-time`. `--retry` only retries a request that fails, so a connection
# that goes quiet without closing blocks forever: observed on 2026-09-03 as a
# single Reservoir request for proofwidgets sitting at 0% CPU for 66 minutes
# while the harness looked alive. Bound each attempt so a hung request falls
# through to the next strategy instead of hanging the run. `timeout` signals
# the whole process group, which is what reaches the curl underneath.
BENCHMARK_CACHE_TIMEOUT="${BENCHMARK_CACHE_TIMEOUT:-1200}"

benchmark_bounded() {
  local seconds="$1"
  shift
  if [[ "$seconds" -le 0 ]] || ! command -v timeout >/dev/null 2>&1; then
    "$@"
    return
  fi
  timeout -k 30 "$seconds" "$@"
}

benchmark_fetch_cache() {
  local project="$1"
  local log="$2"
  local mathlib="$project/.lake/packages/mathlib"
  local limit="$BENCHMARK_CACHE_TIMEOUT"

  # Mathlib's own cache tool first, whenever the corpus carries Mathlib. It is
  # the one with artifacts for this workload: measured on Velvet at v4.32.2 it
  # fetched 8275 oleans in 32s, while `lake cache get` searched Reservoir for
  # 100 revisions over six minutes and reported "no outputs found" for Mathlib,
  # Aesop, Batteries, Qq and the rest -- Reservoir simply has no build outputs
  # for this platform and toolchain. Trying it first cost six wasted minutes on
  # every tree, and there are several trees per corpus.
  if [[ -d "$mathlib" ]]; then
    if (cd "$project" && benchmark_bounded "$limit" lake exe cache get) \
        > "$log" 2>&1; then
      return 0
    fi
    printf '\nRoot cache executable unavailable; trying Mathlib directly.\n' \
      >> "$log"
    if (cd "$mathlib" && benchmark_bounded "$limit" lake exe cache get) \
        >> "$log" 2>&1; then
      return 0
    fi
    printf '\nMathlib cache unavailable; trying the native Lake cache.\n' \
      >> "$log"
  fi

  # No Mathlib, or its cache is down. The native cache is the right tool for a
  # corpus without Mathlib and the last resort for one with it.
  if (cd "$project" && benchmark_bounded "$limit" lake cache get) \
      >> "$log" 2>&1; then
    return 0
  fi
  return 1
}

benchmark_sync_crush_sources() {
  local crush_root="$1"
  local project_tree="$2"
  local package="$project_tree/.lake/packages/crush"

  if [[ ! -d "$package/Crush" ]]; then
    printf 'error: lean-crush dependency not materialized at %s\n' \
      "$package" >&2
    return 1
  fi
  rsync -a --delete "$crush_root/Crush/" "$package/Crush/"
  cp "$crush_root/Crush.lean" "$package/Crush.lean"
}
