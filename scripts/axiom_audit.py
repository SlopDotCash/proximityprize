#!/usr/bin/env python3
"""Axiom audit over the pinned flagship list (scripts/flagship_axioms.txt).

Generates a Lean file importing each flagship module and running
`#print axioms <decl>` for every pinned declaration, compiles it through
`lake env lean`, and fails if:
  - the compile fails (e.g. a pinned declaration no longer exists),
  - any declaration depends on an axiom outside
    {propext, Classical.choice, Quot.sound} (incl. sorryAx, Lean.ofReduceBool
    from native_decide, or any custom axiom),
  - any pinned declaration is missing an axiom report,
  - the axiom inventory below fails.

Axiom inventory: the same Lean file also imports the module of every residual
axiom pinned in scripts/residual_axioms.txt and lists, from Lean's environment
metadata, every axiom constant declared in an `ArkLib`, `ProximityPrize`, or
`Research` module of its import closure. Each one must be a pinned residual with
the same fully qualified name and defining module. Unlike the lexical
precheck (scripts/forbidden_tokens.py) this sees every declaration-name form and
axioms added without the `axiom` keyword (a macro, an elaborator, a native
`decide` auxiliary), but only for modules in that import closure, not for every
retained module; and it checks identity and location, while the reviewed
statement is pinned by the precheck's signature digest. A pinned axiom is a
documented assumption, not a proof.

This is strictly stronger than the compile-only gate: it catches `sorry`
(sorryAx), custom axioms, and silent statement weakening via laundered
dependencies. Run from the ArkLib checkout root after building every module
named in flagship_axioms.txt and residual_axioms.txt (`--print-modules` lists
them).
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

import forbidden_tokens

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MANIFEST = Path(__file__).resolve().parent / "flagship_axioms.txt"
RESIDUALS = Path(__file__).resolve().parent / "residual_axioms.txt"
INVENTORY_TAG = "AXIOM-INVENTORY"
AUDITED_ROOTS = ("ArkLib", "ProximityPrize", "Research")


def inventory_command(roots: tuple[str, ...] = AUDITED_ROOTS) -> str:
    """Lean command printing each axiom declared in an imported module under `roots`.

    Output lines are `AXIOM-INVENTORY<TAB><name><TAB><module>`; private names
    are printed without their `_private` prefix.
    """
    test = " || ".join(f"mod.getRoot == `{root}" for root in roots)
    return (
        "open Lean in\n"
        "#eval show CoreM Unit from do\n"
        "  let env ← getEnv\n"
        "  let names := env.header.moduleNames\n"
        "  let data := env.header.moduleData\n"
        "  for i in [0:names.size] do\n"
        "    let mod := names[i]!\n"
        f"    if {test} then\n"
        "      for c in data[i]!.constants do\n"
        "        if c matches .axiomInfo _ then\n"
        "          let n := (Lean.privateToUserName? c.name).getD c.name\n"
        f'          IO.println s!"{INVENTORY_TAG}\\t{{n}}\\t{{mod}}"\n'
    )


def module_of(path: str) -> str:
    """`ArkLib/A/B.lean` -> `ArkLib.A.B` (the module a pinned file defines)."""
    return path[: -len(".lean")].replace("/", ".") if path.endswith(".lean") else path


def check_inventory(output: str, pins: dict) -> tuple[list[str], list[str]]:
    """Failures and warnings from the inventory lines in Lean's `output`."""
    found: dict[str, str] = {}
    for line in output.splitlines():
        parts = line.split("\t")
        if len(parts) == 3 and parts[0] == INVENTORY_TAG:
            found[forbidden_tokens.canonical_name(parts[1])] = parts[2]
    failures: list[str] = []
    for fqn, module in sorted(found.items()):
        pin = pins.get(fqn)
        if pin is None:
            failures.append(f"{fqn}: axiom declared in {module} is not a residual pinned in "
                            f"scripts/residual_axioms.txt")
        elif module_of(pin.file) != module:
            failures.append(f"{fqn}: axiom declared in {module}, but its pin names {pin.file}")
    warnings = [f"{fqn}: pinned residual is not an axiom of {module_of(pin.file)} in the "
                f"built environment (discharged? remove its entry)"
                for fqn, pin in sorted(pins.items()) if fqn not in found]
    return failures, warnings


# Lean prints `#print axioms foo'` as `'foo'' depends on ...`: a name may end in
# primes, so take the shortest same-line name before the closing quote.
DEP_RE = re.compile(r"(?<!\S)'([^\n]+?)' depends on axioms: \[([^\]]*)\]")
NODEP_RE = re.compile(r"(?<!\S)'([^\n]+?)' does not depend on any axioms")


def main() -> int:
    entries: list[tuple[str, str]] = []
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        module, decl = line.split()
        entries.append((module, decl))
    if not entries:
        print("axiom audit: empty manifest", file=sys.stderr)
        return 1
    pins, manifest_errors = forbidden_tokens.load_manifest(RESIDUALS)
    if manifest_errors:
        print("\n".join(manifest_errors), file=sys.stderr)
        return 1

    modules = sorted({m for m, _ in entries} | {module_of(p.file) for p in pins.values()})
    if sys.argv[1:] == ["--print-modules"]:
        print("\n".join(modules))
        return 0
    src = "import Lean\n" + "\n".join(f"import {m}" for m in modules) + "\n\n"
    src += "\n".join(f"#print axioms {d}" for _, d in entries) + "\n"
    src += inventory_command()

    # Scratch file OUTSIDE the repo: an autosync daemon commits anything that
    # appears in the working tree, including short-lived temp files.
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".lean", delete=False) as tf:
        tf.write(src)
        tmp = Path(tf.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(tmp)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=1800,
        )
    finally:
        tmp.unlink(missing_ok=True)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(out[:4000], file=sys.stderr)
        print("axiom audit: audit file failed to compile (build every module that "
              "`python3 scripts/axiom_audit.py --print-modules` lists first)", file=sys.stderr)
        return 1

    reported: dict[str, set[str]] = {}
    for m in DEP_RE.finditer(out):
        axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
        # Imported diagnostics can repeat a declaration's report. No later
        # report, including a no-dependency line, may erase a forbidden axiom.
        reported.setdefault(m.group(1), set()).update(axioms)
    for m in NODEP_RE.finditer(out):
        reported.setdefault(m.group(1), set())

    failures: list[str] = []
    for _, decl in entries:
        if decl not in reported:
            failures.append(f"{decl}: no axiom report produced")
            continue
        extra = reported[decl] - ALLOWED
        if extra:
            failures.append(f"{decl}: forbidden axioms {sorted(extra)}")
    inventory_failures, inventory_warnings = check_inventory(out, pins)
    failures += inventory_failures
    if inventory_warnings:
        print("WARNING: " + "\nWARNING: ".join(inventory_warnings), file=sys.stderr)

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nAXIOM AUDIT FAILED: {len(failures)} violation(s)", file=sys.stderr)
        return 1
    for _, decl in entries:
        axs = sorted(reported[decl]) or ["<none>"]
        print(f"OK {decl}: {axs}")
    print(f"axiom audit: all {len(entries)} flagship declarations clean; every axiom of the "
          f"audited modules is one of the {len(pins)} pinned residual(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
