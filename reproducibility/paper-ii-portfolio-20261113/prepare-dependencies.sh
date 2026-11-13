#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 || -e "$1" ]]; then
  printf 'Usage: bash prepare-dependencies.sh NEW_MATHLIB_DIRECTORY\n' >&2
  exit 2
fi

package_dir="$(cd "$(dirname "$0")" && pwd)"
mathlib_dir="$1"
mathlib_revision=c44e0c8ee63ca166450922a373c7409c5d26b00b
git init -q "$mathlib_dir"
git -C "$mathlib_dir" remote add origin https://github.com/leanprover-community/mathlib4.git
git -C "$mathlib_dir" fetch --depth 1 origin "$mathlib_revision"
git -C "$mathlib_dir" checkout --detach FETCH_HEAD
test "$(git -C "$mathlib_dir" rev-parse HEAD)" = "$mathlib_revision"

# Scope curl configuration to Mathlib's cache download.
cache_config_dir="$(mktemp -d)"
trap 'rm -rf "$cache_config_dir"' EXIT
printf 'parallel-max = 4\nrate = 4/s\n' > "$cache_config_dir/.curlrc"
modules=()
while IFS= read -r module; do
  [[ "$module" == Mathlib.* ]] || exit 2
  modules+=("$module")
done < "$package_dir/mathlib-imports.txt"
test "${#modules[@]}" -gt 0
cd "$mathlib_dir"
CURL_HOME="$cache_config_dir" lake exe cache get "${modules[@]}"
