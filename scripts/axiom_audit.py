#!/usr/bin/env python3
"""Axiom audit over the pinned flagship list (scripts/flagship_axioms.txt).

Generates a Lean file importing each flagship module and running
`#print axioms <decl>` for every pinned declaration, compiles it through
`lake env lean`, and fails if:
  - the compile fails (e.g. a pinned declaration no longer exists),
  - any declaration depends on an axiom outside
    {propext, Classical.choice, Quot.sound} (incl. sorryAx, Lean.ofReduceBool
    from native_decide, or any custom axiom),
  - any pinned declaration is missing an axiom report.

This is strictly stronger than the compile-only gate: it catches `sorry`
(sorryAx), custom axioms, and silent statement weakening via laundered
dependencies. Run from the ArkLib checkout root after `lake build ArkLib`.
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MANIFEST = Path(__file__).resolve().parent / "flagship_axioms.txt"

DEP_RE = re.compile(r"^'(.*)' depends on axioms: \[([^\]]*)\]", re.MULTILINE)
NODEP_RE = re.compile(r"^'(.*)' does not depend on any axioms", re.MULTILINE)


def main() -> int:
    entries: list[tuple[str, str]] = []
    for raw in MANIFEST.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        module, decl = line.split()
        entries.append((module, decl))
    if not entries:
        print("axiom audit: empty manifest", file=sys.stderr)
        return 1

    modules = sorted({m for m, _ in entries})
    src = "\n".join(f"import {m}" for m in modules) + "\n\n"
    src += "\n".join(f"#print axioms {d}" for _, d in entries) + "\n"

    # Scratch file OUTSIDE the repo: an autosync daemon commits anything that
    # appears in the working tree, including short-lived temp files.
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(src)
        tmp = Path(tf.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            capture_output=True,
            text=True,
            timeout=1800,
        )
    finally:
        tmp.unlink(missing_ok=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(out[:4000], file=sys.stderr)
        print("axiom audit: audit file failed to compile", file=sys.stderr)
        return 1

    reported: dict[str, set[str]] = {}
    for m in DEP_RE.finditer(out):
        axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
        reported[m.group(1)] = axioms
    for m in NODEP_RE.finditer(out):
        reported[m.group(1)] = set()

    failures: list[str] = []
    for _, decl in entries:
        if decl not in reported:
            failures.append(f"{decl}: no axiom report produced")
            continue
        extra = reported[decl] - ALLOWED
        if extra:
            failures.append(f"{decl}: forbidden axioms {sorted(extra)}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nAXIOM AUDIT FAILED: {len(failures)} flagship violation(s)", file=sys.stderr)
        return 1
    for _, decl in entries:
        axs = sorted(reported[decl]) or ["<none>"]
        print(f"OK {decl}: {axs}")
    print(f"axiom audit: all {len(entries)} flagship declarations clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
