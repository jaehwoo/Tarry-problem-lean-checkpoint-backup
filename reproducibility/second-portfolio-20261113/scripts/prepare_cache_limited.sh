#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Scope curl settings to this invocation. Do not modify a user's ~/.curlrc.
cache_config_dir="$(mktemp -d)"
trap 'rm -rf "$cache_config_dir"' EXIT
printf 'parallel-max = 4\nrate = 4/s\n' > "$cache_config_dir/.curlrc"
CURL_HOME="$cache_config_dir" lake exe cache get
