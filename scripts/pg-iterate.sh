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
#
# WHAT ✅ MEANS: the file compiles, the reported axiom set of every `#print axioms` line is
# inside {propext, Classical.choice, Quot.sound} plus the documented residuals of
# `scripts/residual_axioms.txt`, and CI gate 1 (`scripts/forbidden_tokens.py`) accepts the
# file. `requiredTests` records this script as the narrow check for prize work, so a ✅ here
# must not certify a file that `./scripts/validate.sh` rejects.
set -euo pipefail
QUIET=0; [[ "${1:-}" == "-q" ]] && { QUIET=1; shift; }
F="${1:?usage: pg-iterate.sh [-q] <file.lean>}"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RESIDUAL_ALLOWLIST="$REPO_ROOT/scripts/residual_axioms.txt"
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

# CI gate 1 parity. `lake env lean` reports nothing for `axiom`, `native_decide`,
# `bv_decide`, `unsafe`, `@[implemented_by]` or a metaprogram `addDecl`, so the type-check
# above cannot see them; a green ✅ from this script is the narrow evidence `requiredTests`
# asks for, so the whole gate runs here on the same file.
PYTHON_BIN="$(command -v python3 || command -v python || true)"
if [[ -z "$PYTHON_BIN" ]]; then
  echo "❌ FAIL: python3 is required to run CI gate 1 (forbidden_tokens.py) on the file;" >&2
  echo "   without it this narrow check cannot certify axiom cleanliness. Run" >&2
  echo "   ./scripts/validate.sh, or install Python 3 with a CA trust store." >&2
  exit 1
fi
if ! GATE1="$("$PYTHON_BIN" "$REPO_ROOT/scripts/forbidden_tokens.py" "$F" 2>&1)"; then
  echo "❌ FAIL (${ELAPSED}s) — CI gate 1 (forbidden_tokens) rejects $F:"
  printf '%s\n' "$GATE1" | grep -v '^[[:space:]]*$' | head -20
  exit 1
fi

# Axiom audit. `#print axioms` output is the only place a real dependency set appears, and
# `native_decide` reports a generated name (e.g. `foo._native.native_decide.ax_1_1`), not
# `sorryAx`, so checking for `sorryAx` alone never audits anything.
ALLOWED_AXIOMS=$'propext\nClassical.choice\nQuot.sound'
axiom_allowed() {
  # Mirrors `is_allowlisted` in forbidden_tokens.py: a documented residual is
  # matched by its simple name too, so a namespaced declaration still traces to
  # its one allowlist entry.
  local name="$1" simple="${1##*.}"
  grep -qxF -- "$name" <<<"$ALLOWED_AXIOMS" && return 0
  [[ -f "$RESIDUAL_ALLOWLIST" ]] || return 1
  sed -e 's/#.*//' "$RESIDUAL_ALLOWLIST" | awk 'NF {print $1}' \
    | grep -qxF -e "$name" -e "$simple"
}
# Lean wraps the printed list at the message width, so `[a, b,` and `]` can sit on different
# lines. A one-line `sed` capture would then match nothing and audit NOTHING while still
# printing ✅, so carry the open bracket across lines and treat an unterminated list as
# unauditable instead of clean.
AXIOM_SCAN="$(printf '%s\n' "$OUT" | awk '
  BEGIN { marker = "depends on axioms: [" }
  {
    line = $0
    if (!collecting) {
      at = index(line, marker)
      if (at == 0) next
      line = substr(line, at + length(marker))
      collecting = 1
    }
    endpos = index(line, "]")
    if (endpos == 0) { buffer = buffer " " line; next }
    buffer = buffer " " substr(line, 1, endpos - 1)
    count = split(buffer, entry, ",")
    for (i = 1; i <= count; i++) {
      name = entry[i]
      gsub(/^[ \t]+/, "", name); gsub(/[ \t]+$/, "", name)
      if (name != "") print name
    }
    buffer = ""; collecting = 0
  }
  END { if (collecting) exit 3 }
')" && AXIOM_SCAN_OK=1 || AXIOM_SCAN_OK=0
if [[ $AXIOM_SCAN_OK -ne 1 ]]; then
  echo "❌ FAIL (${ELAPSED}s) — a 'depends on axioms' line opens a list that never closes;" >&2
  echo "   the reported axiom set cannot be read, so this run certifies nothing. Re-run" >&2
  echo "   with the full '#print axioms' output." >&2
  exit 2
fi
REPORTED_AXIOMS="$(printf '%s\n' "$AXIOM_SCAN" | sort -u)"
UNAPPROVED=""
if [[ -n "$REPORTED_AXIOMS" ]]; then
  while IFS= read -r AX; do
    [[ -z "$AX" ]] && continue
    axiom_allowed "$AX" || UNAPPROVED+="${AX}"$'\n'
  done <<<"$REPORTED_AXIOMS"
fi
if [[ -n "$UNAPPROVED" ]]; then
  echo "❌ FAIL (${ELAPSED}s) — compiles but is not axiom-clean; unapproved axiom(s):"
  printf '%s' "$UNAPPROVED" | sed 's/^/   /'
  if grep -qF 'sorryAx' <<<"$UNAPPROVED"; then
    echo "   (sorryAx: a declaration in this file still has a live hole)"
  fi
  echo "   allowed: {propext, Classical.choice, Quot.sound} plus the documented"
  echo "   residuals in scripts/residual_axioms.txt; a new residual must be stated as"
  echo "   an explicit axiom and documented there, not laundered."
  exit 2
fi

if [[ $QUIET -eq 0 ]]; then
  printf '%s\n' "$OUT" | grep "depends on axioms" | sed -n '1,10p' || true
fi
echo "✅ OK (${ELAPSED}s) — $F"
