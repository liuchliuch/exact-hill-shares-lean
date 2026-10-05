#!/usr/bin/env bash
# An explicit trust mode is required; there is no silent sandbox downgrade.
set -euo pipefail
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
if [[ -n ${LEAN_HOME:-} ]]; then export PATH="$LEAN_HOME/bin:$PATH"; fi
exec python3 "$ROOT/scripts/compare.py" "$@"
