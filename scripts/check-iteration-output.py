#!/usr/bin/env python3
"""Inspect emitted Lean admission diagnostics, without classifying filenames as errors."""
from __future__ import annotations

import re
import sys

SORRY_WARNING = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:\s*)?warning:\s*declaration uses [`'\"]sorry[`'\"]"
)
AXIOM_REPORT = re.compile(
    r"(?m)^(?:[^\n]*:\d+:\d+:\s*(?:info:\s*)?)?'[^\n]+' depends on axioms:\s*\[([^\]]*)\]"
)
SORRY_AXIOM = re.compile(r"(?<![\w.])sorryAx(?![\w.])")


def main() -> int:
    output = sys.stdin.read()
    for match in AXIOM_REPORT.finditer(output):
        if SORRY_AXIOM.search(match[1]):
            print(match[0])
            return 2
    warnings = [match[0] for match in SORRY_WARNING.finditer(output)]
    if warnings:
        print("\n".join(warnings))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
