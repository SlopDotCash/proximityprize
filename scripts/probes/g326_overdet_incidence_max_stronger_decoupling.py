#!/usr/bin/env python3
"""G326 exact probe: stronger-decoupling chain for the overdet far-line incidence MAX.

Adds three new tight-inequality rungs to the existing G322
`overdetIncidenceMax_gt_double_budget` (`I_max(m) > 8m` for `m >= 3`):

  `overdetIncidenceMax m > 12m` for `m >= 3`  (margin 1 at m=3:  37 > 36)
  `overdetIncidenceMax m > 24m` for `m >= 4`  (margin 1 at m=4:  97 > 96)
  `overdetIncidenceMax m > 40m` for `m >= 5`  (margin 1 at m=5: 201 > 200)

Together with the original `overdetIncidenceMax_gt_budget` (`> 4m` for
`m >= 2`) and the G322 `overdetIncidenceMax_gt_double_budget` (`> 8m` for
`m >= 3`), this forms a chain of TIGHT inequalities (margin exactly 1 at
the boundary `m = m_lo`):

  > 4m   for m >= 2
  > 8m   for m >= 3   (G322)
  > 12m  for m >= 3   (G326 #1)
  > 24m  for m >= 4   (G326 #2)
  > 40m  for m >= 5   (G326 #3)

In general `I_max(m) > 2d(d+1) * m` for `m >= d+1` (any `d >= 1`).
The arithmetic: `2m^3 - 2m^2 + 1 - 2d(d+1)*m = 2m*(m-d-1)*(m+d) + 1 > 0`
for `m >= d+1` (each factor nonneg; the `+1` on the LHS makes it strict).

Two independent implementations agree at every cell:

  (A) direct cubic form:       2 * m^3 - 2 * m^2 + 1
  (B) bulk-plus-one form:      2 * m^2 * (m - 1) + 1
                              (= (A); used as the "non-strict + omega" form
                               in the Lean proof)

We verify for each rung `(c, m_lo)`:
  1. `I_max(m_lo) > c * m_lo` (the boundary case; should be margin = 1)
  2. `I_max(m) > c * m` for all m in [m_lo, 50] (the open range)
  3. The bulk `2m^2*(m-1) >= c*m` holds at every m >= m_lo
     (the non-strict form `nlinarith` proves in Lean)
  4. The margin `I_max(m) - c*m` matches the closed form
     `2m*(m-d-1)*(m+d) + 1` at every m (algebraic check)

All arithmetic is exact Python `int` -- no `float`, no `Fraction` needed,
no `sympy`/`numpy`/`scipy`.

This is a (P) brick: each rung is a (P) Lean kernel theorem proved by
`nlinarith` + `omega`, and the probe carries the exact integer cross-check.
"""
from __future__ import annotations

import sys


# ---------------------------------------------------------------------------
# Two independent implementations
# ---------------------------------------------------------------------------

def I_max_direct(m: int) -> int:
    """Implementation A: the direct cubic form 2*m^3 - 2*m^2 + 1."""
    return 2 * m ** 3 - 2 * m ** 2 + 1


def I_max_bulk_plus_one(m: int) -> int:
    """Implementation B: the bulk-plus-one form 2*m^2*(m-1) + 1.

    Used as the "non-strict + omega" form in the Lean proof: rewrite the
    closed form via `overdetIncidenceMax_eq_bulk_plus_one`, prove the
    non-strict bulk inequality with `nlinarith`, and let `omega` lift the
    `+1` on the LHS to strict `>`.
    """
    return 2 * m ** 2 * (m - 1) + 1


# ---------------------------------------------------------------------------
# The chain
# ---------------------------------------------------------------------------

# TWO kinds of rungs:
#
# (a) The TIGHT-inequality chain: `I_max(m) > 2d(d+1)*m` for `m >= d+1`.
#     At the boundary `m = d+1` the margin is EXACTLY 1 (e.g. `I_max(3) - 12*3
#     = 37 - 36 = 1`). The bulk `2m^2*(m-1) - 2d(d+1)*m = 2m*(m-d-1)*(m+d)`
#     is nonneg for `m >= d+1`; `omega` lifts the `+1` on the LHS to strict.
#
#     d=1: c=4,  m_lo=2  (the original `overdetIncidenceMax_gt_budget`)
#     d=2: c=12, m_lo=3  (G326 #1)
#     d=3: c=24, m_lo=4  (G326 #2)
#     d=4: c=40, m_lo=5  (G326 #3)
#
# (b) The "double budget" rung (a separate, non-tight addition): `I_max(m) > 8m`
#     for `m >= 3` (G322 `overdetIncidenceMax_gt_double_budget`).  This is the
#     natural "double the budget n = 4m" decoupling but does NOT lie on the
#     tight chain (margin at m=3 is 13, not 1).  Proven with the same pattern.

TIGHT_CHAIN = [
    ("I_max(m) > 4m",   4,  2, 1),
    ("I_max(m) > 12m", 12,  3, 2),
    ("I_max(m) > 24m", 24,  4, 3),
    ("I_max(m) > 40m", 40,  5, 4),
]

# The "double budget" rung is a SEPARATE case (not on the tight chain).
DOUBLE_BUDGET = ("I_max(m) > 8m", 8, 3)


def margin_closed_form(m: int, d: int) -> int:
    """The margin `I_max(m) - 2d(d+1)*m` in factored form:
    `2m*(m - d - 1)*(m + d) + 1`.

    For `m = d+1`, this gives `2(d+1)*0*(2d+1) + 1 = 1` (margin 1 at the
    boundary). For `m > d+1`, grows quadratically.

    Derivation:
      I_max(m) = 2m^3 - 2m^2 + 1
      I_max(m) - 2d(d+1)*m = 2m^3 - 2m^2 - 2d(d+1)m + 1
                           = 2m * (m^2 - m - d(d+1)) + 1
                           = 2m * (m - d - 1)(m + d) + 1
        [since (m - d - 1)(m + d) = m^2 + dm - (d+1)m - d(d+1)
                                     = m^2 - m - d(d+1)]
    """
    return 2 * m * (m - d - 1) * (m + d) + 1


def main() -> int:
    rc = 0
    sys.stdout.reconfigure(line_buffering=True)

    # --- (0) two-impl agreement at every m in the full sweep --------------
    print("[0] two-implementation agreement (A = direct cubic, B = bulk+1):")
    fails = 0
    for m in range(2, 51):
        a = I_max_direct(m)
        b = I_max_bulk_plus_one(m)
        if a != b:
            print(f"  MISMATCH at m={m}: A={a} vs B={b}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 49/49 cells: A == B exactly")

    # --- (1) tight chain rungs: tight boundary, open range, bulk, margin ---
    for rung_idx, (name, c, m_lo, d) in enumerate(TIGHT_CHAIN, start=1):
        print()
        print(f"[{rung_idx}] {name} for m >= {m_lo}  (d = {d}, c = 2*d*(d+1) = {c}, TIGHT):")

        # (1a) boundary check: margin = 1 at m = m_lo
        margin_lo = I_max_direct(m_lo) - c * m_lo
        if margin_lo != 1:
            print(f"  [BAD] boundary: I_max({m_lo}) - {c}*{m_lo} = {margin_lo}, expected 1")
            rc = 1
        else:
            print(f"  [OK ] boundary m={m_lo}: I_max={I_max_direct(m_lo):>6}, {c}*{m_lo}={c*m_lo:>4}, margin = {margin_lo} (= 1, tight)")

        # (1b) open range: I_max(m) > c*m for all m in [m_lo, 50]
        fails = 0
        first_fail = None
        for m in range(m_lo, 51):
            if I_max_direct(m) <= c * m:
                if first_fail is None:
                    first_fail = m
                fails += 1
                rc = 1
        n = 51 - m_lo
        if fails == 0:
            print(f"  [OK ] open range: {n}/{n} cells m in [{m_lo}, 50] satisfy I_max(m) > {c}*m")
        else:
            print(f"  [BAD] open range: {fails} failures, first at m={first_fail}")

        # (1c) non-strict bulk: 2*m^2*(m-1) >= c*m for all m >= m_lo
        fails = 0
        first_fail = None
        for m in range(m_lo, 51):
            if 2 * m * m * (m - 1) < c * m:
                if first_fail is None:
                    first_fail = m
                fails += 1
                rc = 1
        if fails == 0:
            print(f"  [OK ] non-strict bulk: {n}/{n} cells m in [{m_lo}, 50] satisfy 2m^2(m-1) >= {c}*m")
        else:
            print(f"  [BAD] non-strict bulk: {fails} failures, first at m={first_fail}")

        # (1d) margin closed-form check: I_max(m) - c*m = 2m(m-d-1)(m+d) + 1
        fails = 0
        for m in range(m_lo, 51):
            actual = I_max_direct(m) - c * m
            expected = margin_closed_form(m, d)
            if actual != expected:
                fails += 1
                rc = 1
        if fails == 0:
            print(f"  [OK ] margin closed form: {n}/{n} cells match 2m(m-d-1)(m+d) + 1 exactly")
        else:
            print(f"  [BAD] margin closed form: {fails} cells do NOT match the closed form")
            rc = 1

    # --- (2) double-budget rung (NOT tight; separate case) ----------------
    print()
    db_name, db_c, db_m_lo = DOUBLE_BUDGET
    print(f"[5] {db_name} for m >= {db_m_lo}  (DOUBLE BUDGET, not on tight chain):")

    fails = 0
    first_fail = None
    for m in range(db_m_lo, 51):
        if I_max_direct(m) <= db_c * m:
            if first_fail is None:
                first_fail = m
            fails += 1
            rc = 1
    n = 51 - db_m_lo
    if fails == 0:
        print(f"  [OK ] open range: {n}/{n} cells m in [{db_m_lo}, 50] satisfy I_max(m) > {db_c}*m")
    else:
        print(f"  [BAD] open range: {fails} failures, first at m={first_fail}")

    fails = 0
    for m in range(db_m_lo, 51):
        if 2 * m * m * (m - 1) < db_c * m:
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  [OK ] non-strict bulk: {n}/{n} cells m in [{db_m_lo}, 50] satisfy 2m^2(m-1) >= {db_c}*m")

    # Margin at the boundary (NOT tight; just shows the gap from the tight chain)
    margin_db = I_max_direct(db_m_lo) - db_c * db_m_lo
    print(f"  [INFO] boundary m={db_m_lo}: I_max={I_max_direct(db_m_lo)}, {db_c}*{db_m_lo}={db_c*db_m_lo}, margin = {margin_db} (not 1; the tight rung at m={db_m_lo} is the 12m one above)")

    # --- (3) margin growth check: margin grows quadratically from boundary
    print()
    print("[6] margin growth from boundary (margin at m = m_lo+k for k=0..5):")
    for name, c, m_lo, d in TIGHT_CHAIN:
        margins = [I_max_direct(m_lo + k) - c * (m_lo + k) for k in range(6)]
        print(f"  {name:>22}:  " + "  ".join(f"{v:>6}" for v in margins))
    db_margins = [I_max_direct(db_m_lo + k) - db_c * (db_m_lo + k) for k in range(6)]
    print(f"  {db_name:>22}:  " + "  ".join(f"{v:>6}" for v in db_margins) + "   (double-budget rung)")

    # --- (4) chain consistency: at every m, the strongest applicable tight rung
    #       gives the tightest bound (margin = 1 at the boundary, larger beyond)
    print()
    print("[7] chain consistency at every m (which tight rung gives the tightest bound?):")
    for m in range(2, 11):
        applicable = [(name, c, d) for (name, c, m_lo, d) in TIGHT_CHAIN if m >= m_lo]
        # pick the rung with the largest c (tightest applicable bound)
        best_name, best_c, _ = max(applicable, key=lambda t: t[1])
        best_margin = I_max_direct(m) - best_c * m
        tight = "*" if best_margin == 1 else " "
        print(f"  m={m:2d}: tightest tight-rung = {best_name:>22}  (margin = {best_margin:>5}){tight}")

    # --- summary -----------------------------------------------------------
    print()
    print("=" * 70)
    if rc == 0:
        print("G326 SUMMARY: stronger-decoupling chain verified at m=2..50.")
        print("  TIGHT chain (margin = 1 at boundary):")
        print("    > 4m  for m >= 2   (original `overdetIncidenceMax_gt_budget`)")
        print("    > 12m for m >= 3   (G326 #1, NEW)")
        print("    > 24m for m >= 4   (G326 #2, NEW)")
        print("    > 40m for m >= 5   (G326 #3, NEW)")
        print("  Double-budget rung (NOT on the tight chain):")
        print("    > 8m  for m >= 3   (G322 `overdetIncidenceMax_gt_double_budget`, margin 13 at m=3)")
        print("All rungs pass. The tight-chain margins grow quadratically from the boundary.")
    else:
        print("G326 SUMMARY: one or more checks FAILED -- see FAIL lines above.")
    print("=" * 70)
    return rc


if __name__ == "__main__":
    sys.exit(main())
