#!/usr/bin/env bash
# Preserve the exporter's own -- separator while using the real Landrun sandbox.
set -euo pipefail
: "${LANDRUN_EXECUTABLE:?Set the absolute path to the pinned Landrun executable}"
options=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --ro|--rox|--rw|--rwx|--env)
      [[ $# -ge 2 ]] || { echo 'Missing Landrun option value' >&2; exit 2; }
      options+=("$1" "$2"); shift 2 ;;
    --best-effort|-ldd|-add-exec)
      options+=("$1"); shift ;;
    --) shift; break ;;
    -*) echo "Unsupported Landrun option: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo 'Missing sandboxed command' >&2; exit 2; }
# Keep the Lean thread limit inside the sandbox.
exec "$LANDRUN_EXECUTABLE" "${options[@]}" --env LEAN_NUM_THREADS -- "$@"
