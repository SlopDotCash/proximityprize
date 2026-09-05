#!/usr/bin/env bash
# pg-iterate.sh — FAST single-file iteration for the Proximity Gap challenge (#334).
#
# WHY: `lake build <module>` traces the whole 3000+-job dependency graph (~2-3 min even
# no-op) and takes the .lake build LOCK (serializes concurrent agents). `lake env lean
# <file>` elaborates ONE file against the already-built oleans — ~30s, NO lock — so many
# agents iterate in parallel on this 16-core box without clogging.
#
# USAGE:
#   scripts/pg-iterate.sh path/to/Frontier.lean        # type-check + axiom audit
#   scripts/pg-iterate.sh -q path/to/Frontier.lean     # quiet (errors only)
#
# REQUIREMENT: the file's imports must already be BUILT (oleans present). Build the
# substrate once with `lake build <SubstrateModule>` (or `lake exe cache get` for mathlib),
# then iterate with this script. Keep frontier imports MINIMAL — import only the specific
# substrate modules you consume, never the whole ProximityGap cone (cuts olean-load time).
set -euo pipefail
QUIET=0; [[ "${1:-}" == "-q" ]] && { QUIET=1; shift; }
F="${1:?usage: pg-iterate.sh [-q] <file.lean>}"
START=$(date +%s)
OUT="$(lake env lean "$F" 2>&1)" && RC=0 || RC=$?
ELAPSED=$(( $(date +%s) - START ))
if (( RC != 0 )); then
  printf '%s\n' "$OUT" >&2
  exit "$RC"
fi
ERRS="$(echo "$OUT" | grep -E 'error|sorry' | grep -viE 'depends on axioms' || true)"
if [[ -n "$ERRS" ]]; then
  echo "❌ FAIL (${ELAPSED}s):"; echo "$ERRS" | head -30; exit 1
fi
# axiom audit (only clean if no sorryAx)
if echo "$OUT" | grep -q "sorryAx"; then
  echo "⚠️  compiles but has sorryAx (not axiom-clean):"; echo "$OUT" | grep -A3 sorryAx | head; exit 2
fi
if [[ $QUIET -eq 0 ]]; then
  printf '%s\n' "$OUT" | grep "depends on axioms" | sed -n '1,10p' || true
fi
echo "✅ OK (${ELAPSED}s) — $F"
