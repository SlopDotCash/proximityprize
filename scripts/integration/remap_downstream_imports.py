#!/usr/bin/env python3
"""Route classic downstream callers through their consolidated extension APIs.

Canonical upstream modules are never rewritten. Re-running the migration is
idempotent; comments, string literals and non-import commands are preserved.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

from extract_downstream_extensions import remap_imports


ROOT = Path(__file__).resolve().parents[2]
RAW_IMPORT = re.compile(r"(?m)^[ \t]*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Report stale callers without writing")
    args = parser.parse_args()
    mapping = json.loads((ROOT / "scripts/integration/downstream-extensions.json").read_text())
    canonical = set(json.loads((ROOT / "scripts/arklib-upstream.json").read_text())["files"])
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "ArkLib/*.lean", "Research/*.lean"], cwd=ROOT
    ).decode().split("\0")
    changed = []
    for relative in paths:
        if not relative or relative in canonical:
            continue
        path = ROOT / relative
        if not path.is_file():
            raise SystemExit(f"Missing tracked downstream source: {relative}")
        original = path.read_text()
        # This is only a fast rejection filter. A candidate is still lexed below,
        # so import-like text in comments or literals cannot change source.
        if not any(token in mapping for match in RAW_IMPORT.finditer(original)
                   for token in match[1].split()):
            continue
        rewritten = remap_imports(original, mapping)
        if rewritten != original:
            changed.append(relative)
            if not args.check:
                path.write_text(rewritten)
    if args.check:
        for path in changed:
            print(path)
        if changed:
            print(f"{len(changed)} downstream callers need import migration.")
            return 1
    else:
        print(f"Migrated imports in {len(changed)} downstream source files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
