#!/usr/bin/env python3
# Copyright (c) 2026 laooooonn. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
# Authors: laooooonn (GitHub: andyboss1995)
"""Check that the staged two-power control digests pinned by the non-two-power column probes
are now published by code that is already tracked in ``main``.

The two probes added by this change pin ten vector digests for the column ``b = n - 1`` at the
two-power rungs ``n = 8, 16, 32, 64, 128`` over the two primes ``65537`` and ``21*2^128+1``.  They
called those numbers "this campaign's UNMERGED staged digests".  This script re-reads both tables
by parsing the two source files (it imports neither probe and recomputes nothing) and reports
whether every pinned digest also appears, with the same value, in the digest table of
``scripts/probes/probe_t3_ceiling_column_high_rungs.py``, which is tracked and unmodified.

What this checks: that the control values the new probes assert against are numbers the repository
already publishes, so a reviewer can compare them with tracked code.  What it does not check: the
arithmetic behind any digest.  Each digest is re-derived from count vectors inside the probes
themselves; nothing here re-computes a census.

Usage: python3 scripts/probes/probe_t3_ceiling_column_non2power_staged_anchor.py [repo-root]
"""
import ast
import pathlib
import sys

NEW_PROBE = "scripts/probes/probe_t3_ceiling_column_non2power.py"
TRACKED_PROBE = "scripts/probes/probe_t3_ceiling_column_high_rungs.py"
NEW_TABLE = "STAGED_TWO_POWER_DIGESTS"
TRACKED_TABLE = "PINNED_VECTOR_DIGESTS"


def table(root: pathlib.Path, rel: str, name: str) -> dict:
    """Return one module-level dict literal, parsed from source, without importing the module."""
    source = (root / rel).read_text(encoding="utf-8")
    brace = source.index("{", source.index(f"{name} = "))
    depth = 0
    for index in range(brace, len(source)):
        depth += source[index] == "{"
        depth -= source[index] == "}"
        if depth == 0:
            return {
                tuple(key) if isinstance(key, list) else key: value
                for key, value in ast.literal_eval(source[brace : index + 1]).items()
            }
    raise AssertionError(f"unbalanced dict for {name} in {rel}")


def main(root: pathlib.Path) -> int:
    pinned = table(root, NEW_PROBE, NEW_TABLE)
    tracked = table(root, TRACKED_PROBE, TRACKED_TABLE)
    print(f"{NEW_PROBE}: {NEW_TABLE} entries: {len(pinned)}")
    print(f"{TRACKED_PROBE}: {TRACKED_TABLE} entries: {len(tracked)} (tracked in main)")
    absent = []
    differ = []
    for key in sorted(pinned, key=lambda k: (str(k[1]), k[0])):
        rung, prime = key
        value = pinned[key]
        if key not in tracked:
            absent.append(key)
            verdict = "ABSENT-FROM-MAIN"
        elif tracked[key] == value:
            verdict = "matches tracked table"
        else:
            differ.append(key)
            verdict = f"DIFFERS ({tracked[key][:12]}...)"
        print(f"  n={rung:<4} p={prime:<14} {value[:16]}...  {verdict}")
    print(f"pinned digests also published by tracked code: {len(pinned) - len(absent) - len(differ)}"
          f" of {len(pinned)}")
    print(f"absent from the tracked table: {len(absent)} {absent}")
    print(f"present with a different value: {len(differ)} {differ}")
    extra = sorted((key for key in tracked if key not in pinned), key=lambda k: (str(k[1]), k[0]))
    print(f"tracked digests this lane does not use ({len(extra)}):")
    for rung, prime in extra:
        print(f"  n={rung:<4} p={prime:<14} {tracked[(rung, prime)][:16]}...")
    if absent or differ:
        print("FAIL: a staged control digest is not the tracked one")
        return 1
    print("PASS: every staged control digest the new probes pin is also pinned, with the same "
          "value, by the tracked probe_t3_ceiling_column_high_rungs.py in main")
    return 0


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without Python optimization to enable the certificate checks.")
    sys.exit(main(pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(".")))
