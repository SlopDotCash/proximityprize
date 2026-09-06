#!/usr/bin/env bash
# Check the library/research boundary and both generated module umbrellas.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
python3 scripts/check-research-boundary.py
backup_dir="$(mktemp -d "${TMPDIR:-/tmp}/proximity-imports.XXXXXX")"
cp ArkLib.lean "$backup_dir/ArkLib.lean"
cp Research/ProximityPrize/All.lean "$backup_dir/Research-All.lean"
restore_original() {
  cp "$backup_dir/ArkLib.lean" ArkLib.lean
  cp "$backup_dir/Research-All.lean" Research/ProximityPrize/All.lean
  rm -rf "$backup_dir"
}
trap restore_original EXIT
./scripts/update-lib.sh
python3 scripts/update-research-lib.py
status=0
if ! cmp -s "$backup_dir/ArkLib.lean" ArkLib.lean; then
  echo 'ArkLib.lean is out of date; run scripts/update-lib.sh.'
  status=1
fi
if ! cmp -s "$backup_dir/Research-All.lean" Research/ProximityPrize/All.lean; then
  echo 'Research All.lean is out of date; run scripts/update-research-lib.py.'
  status=1
fi
exit "$status"
