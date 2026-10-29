#!/usr/bin/env bash
# pg-iterate.sh — FAST single-file iteration for the Proximity Gap challenge (#334).
#
# WHY: `./scripts/lake-locked.sh build <module>` traces the whole 3000+-job dependency graph (~2-3 min even
# no-op) and takes the .lake build LOCK (serializes concurrent agents). `lake env lean
# <file>` elaborates ONE file against the already-built oleans — ~30s, NO lock — so many
# agents iterate in parallel on this 16-core box without clogging.
#
# USAGE:
#   scripts/pg-iterate.sh path/to/Frontier.lean        # type-check + emitted admission checks
#   scripts/pg-iterate.sh -q path/to/Frontier.lean     # quiet (errors only)
#
# REQUIREMENT: the file's imports must already be BUILT (oleans present). Build the
# substrate once with `./scripts/lake-locked.sh build <SubstrateModule>` (or `./scripts/lake-locked.sh exe cache get` for mathlib),
# then iterate with this script. Keep frontier imports MINIMAL — import only the specific
# substrate modules you consume, never the whole ProximityGap cone (cuts olean-load time).
set -euo pipefail
QUIET=0; [[ "${1:-}" == "-q" ]] && { QUIET=1; shift; }
F="${1:?usage: pg-iterate.sh [-q] <file.lean>}"
START=$(date +%s)
OUT="$(lake env lean -DautoImplicit=false "$F" 2>&1)" && RC=0 || RC=$?
ELAPSED=$(( $(date +%s) - START ))
if (( RC != 0 )); then
  printf '%s\n' "$OUT" >&2
  exit "$RC"
fi
# Compiler status above owns compile errors. Inspect only actual admission warnings
# and printed axiom reports here; paths and benign output may contain "errors" or
# "sorry". This does not generate axiom reports for declarations automatically.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEBT="$(printf '%s\n' "$OUT" | python3 "$SCRIPT_DIR/check-iteration-output.py")" && DEBT_RC=0 || DEBT_RC=$?
if (( DEBT_RC != 0 )); then
  printf '❌ Admission check failed (%ss):\n%s\n' "$ELAPSED" "$DEBT" >&2
  exit "$DEBT_RC"
fi
if [[ $QUIET -eq 0 ]]; then
  printf '%s\n' "$OUT" | grep "depends on axioms" | sed -n '1,10p' || true
fi
echo "✅ OK (${ELAPSED}s) — $F"
