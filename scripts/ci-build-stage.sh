#!/usr/bin/env bash

# Build one contiguous stage of a deterministic topological ordering of every
# module in the generated ArkLib barrel. CI carries each stage's oleans into
# the next job, so no hosted runner has to compile the whole project at once.

set -euo pipefail

if [[ $# -ne 2 ]] || ! [[ "$1" =~ ^[0-9]+$ && "$2" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 STAGE_INDEX STAGE_COUNT" >&2
  exit 2
fi

stage_index="$1"
stage_count="$2"
if (( stage_index >= stage_count )); then
  echo "stage index must be less than stage count" >&2
  exit 2
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

mapfile -t modules < <(
  python3 - "$stage_index" "$stage_count" <<'PY'
import re
import sys
from pathlib import Path

index = int(sys.argv[1])
count = int(sys.argv[2])
root_modules = [
    line.removeprefix("import ").strip()
    for line in Path("ArkLib.lean").read_text().splitlines()
    if line.startswith("import ArkLib.")
]
module_set = set(root_modules)
if len(module_set) != len(root_modules):
    raise SystemExit("ArkLib.lean contains duplicate imports")

import_re = re.compile(r"^import\s+(\S+)", re.MULTILINE)
dependencies = {}
for module in root_modules:
    source = Path(module.replace(".", "/") + ".lean")
    if not source.is_file():
        raise SystemExit(f"missing source for {module}: {source}")
    dependencies[module] = sorted(
        dep for dep in import_re.findall(source.read_text()) if dep in module_set
    )

ordered = []
state = {}

def visit(module):
    marker = state.get(module, 0)
    if marker == 2:
        return
    if marker == 1:
        raise SystemExit(f"internal import cycle involving {module}")
    state[module] = 1
    for dependency in dependencies[module]:
        visit(dependency)
    state[module] = 2
    ordered.append(module)

for module in sorted(root_modules):
    visit(module)

start = len(ordered) * index // count
end = len(ordered) * (index + 1) // count
print("\n".join(ordered[start:end]))
PY
)

if (( ${#modules[@]} == 0 )); then
  echo "ERROR: stage $stage_index/$stage_count contains no modules" >&2
  exit 1
fi

echo "Building stage $stage_index/$stage_count (${#modules[@]} root modules)"
printf '  %s\n' "${modules[@]}"
./scripts/lake-locked.sh build "${modules[@]}"
