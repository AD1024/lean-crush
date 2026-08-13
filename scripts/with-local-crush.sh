#!/usr/bin/env bash

set -euo pipefail

if [[ $# -lt 2 ]]; then
  printf 'usage: %s PROJECT_DIR LEAN_ARGS...\n' "$0" >&2
  exit 2
fi

project_dir="$(cd "$1" && pwd)"
shift

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
crush_root="$(cd "$script_dir/.." && pwd)"
crush_lean="$crush_root/.lake/build/lib/lean"

if [[ ! -f "$crush_lean/Crush.olean" ]]; then
  printf 'error: local Crush is not built; run `lake build Crush` first\n' >&2
  exit 1
fi

project_lean_path="$(cd "$project_dir" && lake env printenv LEAN_PATH)"
project_path="$(cd "$project_dir" && lake env printenv PATH)"
lean_bin="$(cd "$project_dir" && lake env which lean)"

lean_path="$crush_lean"
IFS=':' read -r -a path_entries <<< "$project_lean_path"
for entry in "${path_entries[@]}"; do
  case "$entry" in
    */.lake/packages/crush/.lake/build/lib/lean) ;;
    "$crush_lean") ;;
    *) lean_path="$lean_path:$entry" ;;
  esac
done

export LEAN_PATH="$lean_path"
export PATH="$project_path"

cd "$project_dir"
exec "$lean_bin" "$@"
