#!/usr/bin/env bash
# Check the library/research boundary and both generated module umbrellas.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
python3 scripts/integration/check_consolidation.py
python3 scripts/check-research-boundary.py
backup_dir="$(mktemp -d "${TMPDIR:-/tmp}/proximity-imports.XXXXXX")"
cp ArkLib.lean "$backup_dir/ArkLib.lean"
cp lakefile.toml "$backup_dir/lakefile.toml"
cp ArkLib/Extensions.lean "$backup_dir/Extensions.lean"
cp ArkLib/Downstream.lean "$backup_dir/Downstream.lean"
cp ArkLib/Research/ProximityGap/All.lean "$backup_dir/Research-All.lean"
restore_original() {
  cp "$backup_dir/ArkLib.lean" ArkLib.lean
  cp "$backup_dir/lakefile.toml" lakefile.toml
  cp "$backup_dir/Extensions.lean" ArkLib/Extensions.lean
  cp "$backup_dir/Downstream.lean" ArkLib/Downstream.lean
  cp "$backup_dir/Research-All.lean" ArkLib/Research/ProximityGap/All.lean
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
if ! cmp -s "$backup_dir/Research-All.lean" ArkLib/Research/ProximityGap/All.lean; then
  echo 'Research All.lean is out of date; run scripts/update-research-lib.py.'
  status=1
fi
if ! cmp -s "$backup_dir/lakefile.toml" lakefile.toml; then
  echo 'Downstream library ownership is out of date; run scripts/update-lib.sh.'
  status=1
fi
if ! cmp -s "$backup_dir/Extensions.lean" ArkLib/Extensions.lean; then
  echo 'ArkLib/Extensions.lean is out of date; run scripts/update-lib.sh.'
  status=1
fi
if ! cmp -s "$backup_dir/Downstream.lean" ArkLib/Downstream.lean; then
  echo 'ArkLib/Downstream.lean is out of date; run scripts/update-lib.sh.'
  status=1
fi
exit "$status"
