#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

# Authored assets and generated output have separate homes.
DEST="build/site"
mkdir -p "$DEST"
cp -a website/library/. "$DEST/"

# Build the Lean Project Documentation
echo "Fetching Cache..."
./scripts/lake-locked.sh exe cache get

echo "Building Blueprint Declaration Environment..."
./scripts/lake-locked.sh build ArkLibBlueprint

echo "Building Project Documentation..."
./scripts/lake-locked.sh build ArkLib:docs ArkLibExtensions:docs \
    ResearchProximityPrize:docs ProximityPrizeExtensions:docs ArkLibBlueprint:docs

# Build the Blueprint
echo "Building Blueprint..."
uv run --no-project --python 3.12 python scripts/blueprint-ci.py render
./scripts/lake-locked.sh exe checkdecls website/blueprint/lean_decls

# Prepare the Website Directory
echo "Assembling Website..."
mkdir -p "$DEST/docs"

# Copy Documentation
if [ -d ".lake/build/doc" ]; then
    echo "Copying docs..."
    cp -a .lake/build/doc/. "$DEST/docs/"
else
    echo "Error: Docs build directory not found." >&2
    exit 1
fi

echo "Website build complete in $DEST/"

# Inject Global Navigation
echo "Injecting Global Navigation..."
if [ -f "scripts/inject_nav.py" ]; then
    uv run --no-project --python 3.12 python scripts/inject_nav.py "$DEST"
fi

echo "Open $DEST/index.html to view."
