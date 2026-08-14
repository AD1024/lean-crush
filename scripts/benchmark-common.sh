#!/usr/bin/env bash

benchmark_is_git_repo() {
  git -C "$1" rev-parse --git-dir >/dev/null 2>&1
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

  if ! git -C "$destination" rev-parse --verify \
      "${revision}^{commit}" >/dev/null 2>&1; then
    printf 'Fetching %s revision %s\n' "$label" "$revision" >&2
    if ! git -C "$destination" fetch --filter=blob:none origin \
        "$revision" >&2; then
      git -C "$destination" fetch --filter=blob:none origin >&2 ||
        return 1
    fi
  fi

  if ! git -C "$destination" rev-parse --verify \
      "${revision}^{commit}" >/dev/null 2>&1; then
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
