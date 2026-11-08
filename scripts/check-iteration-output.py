#!/usr/bin/env python3
"""Audit emitted Lean axioms and admissions without classifying filenames as errors."""
from __future__ import annotations

import re
import sys

from forbidden_tokens import ALLOWLIST_PATH, canonical_name, load_manifest

SORRY_WARNING = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:\s*)?warning:\s*declaration uses [`'\"]sorry[`'\"]"
)
AXIOM_REPORT_START = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:[ \t]*(?:info:[ \t]*)?)?"
    r"'[^\n]+' depends on axioms:[ \t]*\["
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    output = sys.stdin.read()
    # `#print axioms` reports fully qualified names; a manifest pin is one such name.
    pins, manifest_errors = load_manifest(ALLOWLIST_PATH)
    if manifest_errors:
        print("\n".join(manifest_errors))
        return 2
    starts = list(AXIOM_REPORT_START.finditer(output))
    unapproved: set[str] = set()
    for index, start in enumerate(starts):
        limit = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        end = output.find("]", start.end(), limit)
        if end == -1:
            print("A reported axiom list never closes.")
            return 2
        for entry in output[start.end():end].split(","):
            name = entry.strip()
            if name and name not in STANDARD_AXIOMS and (
                name == "sorryAx" or canonical_name(name) not in pins
            ):
                unapproved.add(name)
    if unapproved:
        print("Unapproved axiom(s): " + ", ".join(sorted(unapproved)))
        return 2
    warnings = [match[0] for match in SORRY_WARNING.finditer(output)]
    if warnings:
        print("\n".join(warnings))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
