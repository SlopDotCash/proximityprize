#!/usr/bin/env python3
"""Fail when a build log contains warnings that match a scoped warning budget."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check a build log for warnings under selected path prefixes."
    )
    parser.add_argument("log_file", help="Path to the captured build log.")
    parser.add_argument(
        "--path-prefix",
        action="append",
        default=[],
        help="Only match warnings whose path starts with this prefix. Repeatable.",
    )
    parser.add_argument(
        "--source-inventory",
        type=Path,
        help="Only match the files in a reviewed upstream inventory (plus ArkLib.lean).",
    )
    parser.add_argument(
        "--exclude-substring",
        action="append",
        default=[],
        help="Ignore matching warnings that contain this substring. Repeatable.",
    )
    parser.add_argument(
        "--label",
        default="matching warnings",
        help="Human-readable name for the warning class being checked.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    log_path = Path(args.log_file)
    lines = log_path.read_text(encoding="utf-8").splitlines()

    prefixes = tuple(f"warning: {prefix}" for prefix in args.path_prefix)
    source_files = None
    if args.source_inventory:
        source_files = set(json.loads(args.source_inventory.read_text())["files"])
        source_files.add("ArkLib.lean")
    offenders: list[str] = []

    for line in lines:
        if not line.startswith("warning: "):
            continue
        if prefixes and not line.startswith(prefixes):
            continue
        if source_files is not None and line[len("warning: "):].split(":", 1)[0] not in source_files:
            continue
        if any(substr in line for substr in args.exclude_substring):
            continue
        offenders.append(line)

    if not offenders:
        print(f"No {args.label} found.")
        return 0

    print(f"ERROR: Found {len(offenders)} {args.label}:", file=sys.stderr)
    for line in offenders:
        print(line, file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
