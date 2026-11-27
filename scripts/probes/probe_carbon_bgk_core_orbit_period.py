#!/usr/bin/env python3
"""Lightweight (<0.5s) arithmetic & style-lint verifier for Milestone 3 (Analytic CORE Orbit & Period Laws)."""

from __future__ import annotations

import sys
from pathlib import Path

from probe_carbon_bgk_lint_and_bridge import lint_lean_file


def verify_core_orbit_period_arithmetic() -> None:
    n = 1 << 30
    p1 = n * ((1 << 128) + 192) + 1
    p2 = n * (2 * (1 << 128) + 13) + 1

    # Verify injectivity of k -> k^(2^30) mod P_1 and P_2 on 1..32
    vals_p1 = [pow(k, n, p1) for k in range(1, 33)]
    vals_p2 = [pow(k, n, p2) for k in range(1, 33)]
    assert len(set(vals_p1)) == 32, "Collision in 1..32 on P1!"
    assert len(set(vals_p2)) == 32, "Collision in 1..32 on P2!"
    assert vals_p1[0] == 1 and 1 not in vals_p1[1:]
    assert vals_p2[0] == 1 and 1 not in vals_p2[1:]

    # Verify all 32 * 31 = 992 nontrivial fractions +-a/b (1 <= a != b <= 32) avoid mu_{2^30}
    for p in (p1, p2):
        for a in range(1, 33):
            for b in range(1, 33):
                if a != b:
                    inv_b = pow(b, p - 2, p)
                    assert pow((a * inv_b) % p, n, p) != 1
                    assert pow(((p - a) * inv_b) % p, n, p) != 1

    print(
        "[OK] Core orbit & period arithmetic verified: 32 distinct cyclotomic cosets and "
        "992 signed rational exclusions (+-a/b, 1 <= a != b <= 32) confirmed on both P1 and P2."
    )


def main() -> int:
    verify_core_orbit_period_arithmetic()
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
