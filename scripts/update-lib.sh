#!/usr/bin/env bash

# Update ArkLib.lean with the standalone Proximity Prize import surface.
# The broader ArkLib substrate stays in-tree and is compiled transitively when the
# prize modules depend on it; unrelated proof-system experiments are not default targets.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

if [[ ! -d "ArkLib" || ! -f "ArkLib.lean" ]]; then
  echo "ERROR: Run this script from inside the ArkLib repository." >&2
  exit 1
fi

untracked_lean_files=()
while IFS= read -r file; do
  if [[ -n "$file" ]]; then
    untracked_lean_files+=("$file")
  fi
done < <(git ls-files --others --exclude-standard -- 'ArkLib/*.lean')

if (( ${#untracked_lean_files[@]} > 0 )); then
  echo "ERROR: Untracked Lean files under ArkLib/ are not included in ArkLib.lean generation." >&2
  echo "Stage them first, then rerun this script:" >&2
  printf '  git add %q\n' "${untracked_lean_files[@]}" >&2
  exit 1
fi

echo "Updating ArkLib.lean with tracked Proximity Prize imports..."

tmp_file="$(mktemp "${TMPDIR:-/tmp}/arklib-imports.XXXXXX")"
cleanup() {
  rm -f "$tmp_file"
}
trap cleanup EXIT

# Tracked experimental lanes whose direct elaboration exceeds the normal CI
# budget.  They remain available for explicit `pg-iterate.sh` checks.
readonly UMBRELLA_IMPORT_EXCLUDES_RE='^(ArkLib/ToMathlib/GHSZ02LargeNProof\.lean|ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FSMA_SecondMomentPairPartition\.lean|ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FSMC_ForcedCoreSpread\.lean|ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSharedFreshTripleRefuted\.lean|ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterCommonFactorConcreteLocatorAttempt\.lean)$'

{
  git ls-files -- 'ArkLib/Data/CodingTheory/ProximityGap.lean'
  git ls-files -- 'ArkLib/Data/CodingTheory/ProximityGap/*.lean'
} \
  | grep -Ev "$UMBRELLA_IMPORT_EXCLUDES_RE" \
  | LC_ALL=C sort \
  | sed 's/\.lean//;s,/,.,g;s/^/import /' \
  | sed -E 's/([.])([0-9][^.]*)/\1«\2»/g' > "$tmp_file"

if grep -q $'\r$' ArkLib.lean; then
  perl -0pi -e 's/\n/\r\n/g' "$tmp_file"
fi

mv "$tmp_file" ArkLib.lean
trap - EXIT

echo "✓ ArkLib.lean updated with $(grep -c '^import ' ArkLib.lean) imports"
