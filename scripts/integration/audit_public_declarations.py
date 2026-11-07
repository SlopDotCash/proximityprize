#!/usr/bin/env python3
"""Find repeated public declaration names in tracked production and Research sources.

This lexical ownership audit is not a Lean elaborator. In particular, exports,
notations and automatically generated declarations are left to actual module
compilation. Module-default private declarations are deliberately excluded.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

from extract_downstream_extensions import (
    DECL_KINDS, lexical_mask, normalize_command, parse_commands,
)


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOTS = ("ArkLib", "ProximityPrize", "Research")
PUBLIC = re.compile(r"(?:@\[[^\]]*\]\s*)*public\s")


def public_declarations(source: str) -> list[dict]:
    """Track visibility through namespace/section scopes, including public sections."""
    commands = parse_commands(source, strict=False)
    masked, _ = lexical_mask(source)
    visibility = [not any(command.kind == "module" for command in commands)]
    records = []
    for command in commands:
        explicit_public = bool(PUBLIC.match(masked[command.token_start:command.end]))
        visible = (visibility[-1] or explicit_public) and not command.private
        if command.kind in DECL_KINDS and command.full_name and visible:
            normalized = normalize_command(source[command.start:command.end])
            records.append({
                "name": command.full_name,
                "line": command.line,
                "kind": command.kind,
                "command_sha256": hashlib.sha256(normalized.encode()).hexdigest(),
            })
        if command.kind in ("namespace", "section"):
            visibility.append(False if command.private else visibility[-1] or explicit_public)
        elif command.kind == "end" and len(visibility) > 1:
            visibility.pop()
    return records


def audit(root: Path = ROOT, limit: int = 50) -> dict:
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", *SOURCE_ROOTS], cwd=root,
    ).decode().split("\0")
    owners = defaultdict(list)
    failures = []
    inventory = hashlib.sha256()
    source_count = record_count = 0
    for path in sorted(set(paths)):
        file = root / path
        if not path.endswith(".lean") or not file.is_file():
            continue
        source = file.read_bytes()
        source_count += 1
        inventory.update(path.encode() + b"\0" + hashlib.sha256(source).digest())
        try:
            records = public_declarations(source.decode())
        except (ValueError, UnicodeError) as error:
            failures.append({"path": path, "error": str(error)})
            continue
        for record in records:
            name = record.pop("name")
            owners[name].append({"path": path, **record})
            record_count += 1
    duplicates = {name: declarations for name, declarations in sorted(owners.items())
                  if len(declarations) > 1}
    return {
        "method": "Tracked named public commands, with module-default privacy and nested scope visibility.",
        "limitations": "Lexical candidate audit; exports, syntax and generated names require actual Lean compilation.",
        "source_roots": list(SOURCE_ROOTS),
        "source_files": source_count,
        "source_inventory_sha256": inventory.hexdigest(),
        "public_named_records": record_count,
        "duplicate_names": len(duplicates),
        "duplicates": dict(list(duplicates.items())[:limit]),
        "duplicates_truncated": len(duplicates) > limit,
        "parse_failure_count": len(failures),
        "parse_failures": failures[:limit],
        "parse_failures_truncated": len(failures) > limit,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the bounded JSON report to this path.")
    parser.add_argument("--limit", type=int, default=50, help="Maximum reported names/failures (default: 50).")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    report = audit(limit=args.limit)
    if args.output:
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"Public declaration audit: {report['public_named_records']} records; "
          f"{report['duplicate_names']} repeated names; {report['parse_failure_count']} parse failures")
    if not args.output:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    return int(bool(report["duplicate_names"] or report["parse_failure_count"]))


if __name__ == "__main__":
    raise SystemExit(main())
