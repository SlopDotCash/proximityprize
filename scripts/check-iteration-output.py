#!/usr/bin/env python3
"""Audit emitted Lean axioms and admissions without classifying filenames as errors."""
from __future__ import annotations

import re
import sys

from forbidden_tokens import ALLOWLIST_PATH, canonical_name, load_manifest
from lean_lexer import NAME

SORRY_WARNING = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:\s*)?warning:\s*declaration uses [`'\"]sorry[`'\"]"
)
AXIOM_REPORT_START = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:[ \t]*(?:info:[ \t]*)?)?"
    r"'[^\n]+' depends on axioms:[ \t]*\["
)
# A quoted name component can contain a comma or a closing bracket.
AXIOM_REPORT_SEPARATOR = re.compile(r"«[^»]*»|[,\]]")
AXIOM_NAME = re.compile(NAME)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    output = sys.stdin.read()
    residuals, manifest_errors = load_manifest(ALLOWLIST_PATH)
    if manifest_errors:
        print("\n".join(manifest_errors))
        return 2
    starts = list(AXIOM_REPORT_START.finditer(output))
    unapproved: set[str] = set()
    for index, start in enumerate(starts):
        limit = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        entry_start = start.end()
        for token in AXIOM_REPORT_SEPARATOR.finditer(output, entry_start, limit):
            if token[0].startswith("«"):
                continue
            name = output[entry_start:token.start()].strip()
            if AXIOM_NAME.fullmatch(name):
                name = canonical_name(name)
            if name and name not in STANDARD_AXIOMS and (
                name == "sorryAx" or name not in residuals
            ):
                unapproved.add(name)
            if token[0] == "]":
                break
            entry_start = token.end()
        else:
            print("A reported axiom list never closes.")
            return 2
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
