#!/usr/bin/env bash
# Explicit development adapter for the official Comparator; no process isolation.
set -euo pipefail
while [[ $# -gt 0 ]]; do
  case "$1" in
    --ro|--rox|--rw|--rwx|--env) [[ $# -ge 2 ]] || exit 2; shift 2 ;;
    --best-effort|-ldd|-add-exec) shift ;;
    --) shift; break ;;
    -*) echo "Unsupported Landrun option: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || exit 2
exec "$@"
