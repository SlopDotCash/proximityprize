#!/usr/bin/env bash

# Build a deterministic subset of the modules listed by the generated root
# barrel. The union of shards is exactly the ordinary `lake build ArkLib`
# project surface, while each hosted runner stays below its lifetime limit.

set -euo pipefail

if [[ $# -ne 2 ]] || ! [[ "$1" =~ ^[0-9]+$ && "$2" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 SHARD_INDEX SHARD_COUNT" >&2
  exit 2
fi

shard_index="$1"
shard_count="$2"
if (( shard_index >= shard_count )); then
  echo "shard index must be less than shard count" >&2
  exit 2
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

mapfile -t modules < <(
  python3 - "$shard_index" "$shard_count" <<'PY'
import hashlib
import sys
from pathlib import Path

index = int(sys.argv[1])
count = int(sys.argv[2])
modules = []
for line in Path("ArkLib.lean").read_text().splitlines():
    if not line.startswith("import ArkLib."):
        continue
    module = line.removeprefix("import ").strip()
    bucket = int.from_bytes(hashlib.sha256(module.encode()).digest()[:8], "big") % count
    if bucket == index:
        modules.append(module)
print("\n".join(sorted(modules)))
PY
)

if (( ${#modules[@]} == 0 )); then
  echo "ERROR: shard $shard_index/$shard_count contains no modules" >&2
  exit 1
fi

echo "Building shard $shard_index/$shard_count (${#modules[@]} root modules)"
printf '  %s\n' "${modules[@]}"

build_log="$(mktemp "${TMPDIR:-/tmp}/arklib-ci-shard.XXXXXX")"
trap 'rm -f "$build_log"' EXIT

./scripts/lake-locked.sh build "${modules[@]}" 2>&1 | tee "$build_log"

python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLib/Data/ \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib/Data non-sorry warnings'
