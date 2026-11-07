#!/bin/zsh

set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  echo "usage: $0 <command> [args ...]" >&2
  exit 2
fi

exec caffeinate -dimsu "$@"
