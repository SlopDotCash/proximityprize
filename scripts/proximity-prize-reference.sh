#!/usr/bin/env bash
# Build the pinned reference in its own toolchain; never run submission workflows.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
reference="$root/external/proximity-prize"
expected=ed2b68c4a330d76dc4ab6693eec81b685b493270
if [[ ! -f "$reference/lean-toolchain" ]]; then
  echo 'Initialize with: git submodule update --init external/proximity-prize' >&2
  exit 1
fi
if [[ "$(git -C "$reference" rev-parse HEAD)" != "$expected" ]]; then
  echo 'Reference commit differs from the reviewed pin; update the audit before building.' >&2
  exit 1
fi
if [[ -n "$(git -C "$reference" status --porcelain --untracked-files=no)" ]]; then
  echo 'Reference tracked sources are modified; refusing an unreviewed build.' >&2
  exit 1
fi
cd "$reference"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
case "${1:-}" in
  cache) exec "$root/scripts/lake-locked.sh" exe cache get ;;
  targets) exec "$root/scripts/lake-locked.sh" build ProximityPrize ;;
  lower) exec "$root/scripts/lake-locked.sh" build ProximityPrize.SubmissionLower.Solution ;;
  upper) exec "$root/scripts/lake-locked.sh" build ProximityPrize.SubmissionUpper.Solution ;;
  replay-upper) exec lake env lean "$root/scripts/proximity-prize-upper-replay.lean" ;;
  *) echo "Usage: $0 {cache|targets|lower|upper|replay-upper}" >&2; exit 2 ;;
esac
