#!/usr/bin/env python3
"""Lightweight (<0.5s) single-threaded style-linter & arithmetic sanity check for @bgk-core.

Replicates all source-level checks of `scripts/LintStyle/Checks.lean` plus checks zero
`sorry`/`admit`/`axiom`, `set_option autoImplicit false`, and verifies all numerical
constants used in `CarbonBGKPrizeBridgeResolution.lean`.
"""

from __future__ import annotations

import math
import re
import sys
from pathlib import Path

FORBIDDEN_OPTIONS = (
    "set_option linter.",
    "set_option pp.",
    "set_option profiler.",
    "set_option trace.",
    "set_option maxHeartbeats",
    "set_option maxRecDepth",
    "set_option synthInstance.",
)


def lint_lean_file(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    errors: list[str] = []

    if len(lines) > 1500:
        errors.append(f"ERR_NUM_LIN: {len(lines)} lines > 1500")

    if len(lines) < 5 or lines[0] != "/-":
        errors.append("ERR_COP: line 1 must be '/-'")
    if len(lines) >= 2 and not lines[1].startswith("Copyright (c) 20"):
        errors.append("ERR_COP: line 2 must start with 'Copyright (c) 20'")

    authors_found = False
    close_header_idx = None
    for idx, line in enumerate(lines[:15]):
        if line.startswith("Authors:"):
            authors_found = True
            if not line.startswith("Authors: ") or "  " in line or " and " in line or line.endswith("."):
                errors.append(f"ERR_AUT (line {idx + 1}): malformed Authors line: {line!r}")
        if idx > 0 and line == "-/":
            close_header_idx = idx
            break
    if not authors_found:
        errors.append("ERR_AUT: missing Authors line")
    if close_header_idx is None:
        errors.append("ERR_COP: header comment not closed")

    if "set_option autoImplicit false" not in text:
        errors.append("MISSING_AUTOIMPLICIT: must contain 'set_option autoImplicit false'")
    if "/-!" not in text:
        errors.append("ERR_MOD: missing '/-!' module docstring")

    in_block_comment = False
    for idx, line in enumerate(lines, start=1):
        if len(line) > 100 and "http" not in line:
            errors.append(f"ERR_LIN (line {idx}): length {len(line)} > 100: {line}")
        if line.endswith(" ") or line.endswith("\t"):
            errors.append(f"ERR_TWS (line {idx}): trailing whitespace")
        if " ;" in line:
            errors.append(f"ERR_SEM (line {idx}): space before semicolon")
        for opt in FORBIDDEN_OPTIONS:
            if opt in line:
                errors.append(f"ERR_OPT/BUDGET (line {idx}): forbidden '{opt}'")
        if "@[nolint" in line:
            errors.append(f"ERR_NOLINT (line {idx}): forbidden @[nolint]")
        if line in ("import Mathlib", "import ArkLib", "import Batteries", "import Mathlib.Tactic"):
            errors.append(f"ERR_ROOT_IMPORT/TAC (line {idx}): {line}")

        stripped = line.strip()
        if "/-" in line and "-/" not in line:
            in_block_comment = True
        elif "-/" in line:
            in_block_comment = False

        if not in_block_comment and not stripped.startswith("--"):
            if re.search(r"\bsorry\b", line):
                errors.append(f"ERR_SORRY (line {idx}): {line}")
            if re.search(r"\badmit\b", line):
                errors.append(f"ERR_ADMIT (line {idx}): {line}")
            if stripped.startswith("axiom "):
                errors.append(f"ERR_AXIOM (line {idx}): {line}")
            if stripped == "by":
                errors.append(f"ERR_IBY (line {idx}): isolated 'by'")
            if stripped == "·" or re.match(r"^\s*\.\s", line):
                errors.append(f"ERR_DOT (line {idx}): isolated '·' or '. ' bullet")
            if stripped.startswith(":") or stripped.startswith(":="):
                errors.append(f"ERR_CLN (line {idx}): leading ':' or ':='")
            if re.match(r"^\s+simp(\s+--.*)?$", line):
                errors.append(f"ERR_NSP (line {idx}): bare simp (verify it closes goal)")

        if re.match(r"^\s*--\s*(theorem|lemma|def|structure|instance)\s", line):
            errors.append(f"ERR_COMMENT_DECL (line {idx}): commented-out declaration")

        if re.match(r"^(theorem|lemma|def)\s", line):
            if ":=" not in line and not line.endswith("where") and idx < len(lines):
                nxt = lines[idx]
                indent = len(nxt) - len(nxt.lstrip(" "))
                if not nxt.lstrip(" ").startswith("| ") and indent != 4:
                    errors.append(
                        f"ERR_IND (line {idx + 1}): expected 4-space indent after '{line[:30]}...', got {indent}"
                    )

    return errors


def verify_bridge_arithmetic() -> None:
    n = 1 << 30
    p1 = n * ((1 << 128) + 192) + 1
    p2 = n * (2 * (1 << 128) + 13) + 1
    assert p1 == 365375409332725729550921208179070755120141565953
    assert p2 == 730750818665451459101842416358141509841924915201
    assert p1 // (1 << 128) == n
    assert p2 // (1 << 128) == 2 * n

    # Check P2 rate 1/8 separation radius 694116763 / 2^30 > johnson(2^27)
    k8 = 1 << 27
    e_list = 694116763
    assert e_list <= n
    assert (n - e_list) ** 2 < n * (k8 - 1)  # strictly above Johnson
    assert (n - (e_list - 1)) ** 2 > n * (k8 - 1)  # 694116762 is strictly below Johnson
    assert 1660990722 <= p2 // (1 << 128)

    # Check SmoothTwoHeadProduction parameters for rate 1/8 and rate 1/16
    for k, a, b_max, first_max in [
        (1 << 27, 7 * (1 << 26), 1163220311, 581610155),
        (1 << 26, 15 * (1 << 25), 1297438039, 648719019),
    ]:
        assert k + 2 * a == n
        assert n < 3 * a
        assert 128 <= k and 186 * k <= 29 * n
        margin = 3
        agreements = (n + 3 * (k - 1) + margin - 1) // 3 + 1
        assert agreements <= n - (b_max // 2) + 1
        assert b_max // 2 == first_max
        assert first_max < n
        assert (n - first_max) ** 2 > n * (k - 1)  # strictly below Johnson!

    # Check narrow sixth-moment prime window [2^158, 2^158 + 2^144] fits inside B <= 1163220311
    b_narrow_hi = ((1 << 158) + (1 << 144)) // (1 << 128)
    assert b_narrow_hi == (1 << 30) + (1 << 16) == 1073807360
    assert b_narrow_hi <= 1163220311

    print(
        f"[OK] Bridge arithmetic verified: P1//{2**128}={n}, P2//{2**128}={2*n}, "
        f"e_list={e_list} > J(1/8)*n={n * (1 - math.sqrt((k8 - 1) / n)):.2f}, "
        f"smooth two-head window B <= 1,163,220,311 covers [2^158, 2^158+2^144] (B <= {b_narrow_hi})."
    )


def main() -> int:
    verify_bridge_arithmetic()
    failed = False
    for arg in sys.argv[1:]:
        p = Path(arg)
        errs = lint_lean_file(p)
        if errs:
            failed = True
            print(f"[FAIL] {p}:")
            for e in errs:
                print(f"  {e}")
        else:
            print(f"[OK] Lint clean: {p} ({len(p.read_text().splitlines())} lines)")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
