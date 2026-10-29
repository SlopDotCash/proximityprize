#!/usr/bin/env bash
# Regenerate the canonical ArkLib umbrella and downstream library ownership.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
python3 scripts/update-library-surfaces.py
