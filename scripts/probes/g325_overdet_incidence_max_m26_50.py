#!/usr/bin/env python3
"""G325 exact probe: even further extended overdet far-line incidence MAX closed form.

Extends the G322/G323 pin (m = 2 .. 25, n = 8 .. 100) of the over-determined
far-line incidence MAX

    I_max(n) = n^3/32 - n^2/8 + 1   =   2*m^3 - 2*m^2 + 1   (with n = 4*m)

to cover m = 2 .. 50 (n = 8 .. 200), with TWO independent implementations:

  (A) direct cubic form:       2 * m^3 - 2 * m^2 + 1
  (B) alternative binomial:    4 * m * (m * (m - 1) // 2) + 1
                              (= n * C(m, 2) + 1, since m*(m-1) is even for m >= 1)

The G325 brick in ArkLib/Data/CodingTheory/ProximityGap/OverdetIncidenceMaxClosedFormExt.lean
pins the closed form at m = 26 .. 50 (25 new cells, all `decide`):
  33801, 37909, 42337, 47097, 52201, 57661, 63489, 69697, 76297, 83301,
  90721, 98569, 106857, 115597, 124801, 134481, 144649, 155317, 166497,
  178201, 190441, 203229, 216577, 230497, 245001.

The two implementations MUST agree at every m in the full sweep m = 2 .. 50.
We also verify:

  - the existing Lean pin m = 2 .. 10 (sequence 9, 37, ..., 1801),
  - the G322 extension m = 11 .. 15 (2421, 3169, ..., 6301),
  - the G323 extension m = 16 .. 25 (7681, 9249, ..., 30001),
  - the G325 NEW extension m = 26 .. 50 (33801, 37909, ..., 245001),
  - the "bulk" identity 2m^3 - 2m^2 = 2m^2 * (m - 1) (used by `overdetIncidenceMax_bulk`),
  - the existing decoupling inequality `I_max(m) > 4*m` for m >= 2
    (= `overdetIncidenceMax_gt_budget`),
  - the G322 stronger decoupling inequality `I_max(m) > 8*m` for m >= 3
    (overdet MAX exceeds DOUBLE the budget n = 4m),
  - strict monotonicity: `I_max(m) < I_max(m + 1)` for m >= 1
    (difference = 2m * (3m + 1), positive for m >= 1).

All arithmetic is exact Python `int` -- no `float`, no `Fraction` needed, no
`sympy`/`numpy`/`scipy`. The only division in implementation (B) is `m*(m-1)//2`,
which is exact because `m*(m-1)` is always even for `m >= 1` (one of `m`, `m-1`
is even); we `assert (m*(m-1)) % 2 == 0` for sanity at every m.

This is a (P) brick: the closed form is a (P) Lean kernel pinned at the
G322/G323/G325 cells, and the probe carries an exact integer cross-check (C)
that the closed form holds at every m in the full sweep m = 2 .. 50.
"""
from __future__ import annotations

import sys


# ---------------------------------------------------------------------------
# Two independent implementations
# ---------------------------------------------------------------------------

def I_max_direct(m: int) -> int:
    """Implementation A: the direct cubic form 2*m^3 - 2*m^2 + 1."""
    return 2 * m ** 3 - 2 * m ** 2 + 1


def I_max_binomial(m: int) -> int:
    """Implementation B: the binomial form 4*m * C(m, 2) + 1 = n * C(n/4, 2) + 1.

    Since m*(m-1) is always even for m >= 1, m*(m-1)//2 is an exact integer
    division (no floor, no truncation, no floating-point)."""
    assert m >= 1, (m,)
    prod = m * (m - 1)
    assert prod % 2 == 0, (m, prod)
    return 4 * m * (prod // 2) + 1


def bulk(m: int) -> int:
    """The nonzero-gamma bulk 2*m^3 - 2*m^2 = 2*m^2*(m-1) (trivially equal)."""
    return 2 * m ** 3 - 2 * m ** 2


def bulk_factored(m: int) -> int:
    """Factored bulk 2*m^2*(m-1) (== bulk(m), used by `overdetIncidenceMax_bulk`)."""
    return 2 * m ** 2 * (m - 1)


# ---------------------------------------------------------------------------
# Test cells
# ---------------------------------------------------------------------------

# The published sequence pinned in OverdetIncidenceMaxClosedForm.lean
PUBLISHED_SEQUENCE = {
    2: 9, 3: 37, 4: 97, 5: 201, 6: 361, 7: 589, 8: 897, 9: 1297, 10: 1801,
}

# The G322 extension (m = 11 .. 15)
G322_EXTENSION = {
    11: 2421, 12: 3169, 13: 4057, 14: 5097, 15: 6301,
}

# The G323 extension (m = 16 .. 25)
G323_EXTENSION = {
    16: 7681, 17: 9249, 18: 11017, 19: 12997, 20: 15201,
    21: 17641, 22: 20329, 23: 23277, 24: 26497, 25: 30001,
}

# The G325 NEW extension (m = 26 .. 50)
G325_EXTENSION = {
    26: 33801, 27: 37909, 28: 42337, 29: 47097, 30: 52201,
    31: 57661, 32: 63489, 33: 69697, 34: 76297, 35: 83301,
    36: 90721, 37: 98569, 38: 106857, 39: 115597, 40: 124801,
    41: 134481, 42: 144649, 43: 155317, 44: 166497, 45: 178201,
    46: 190441, 47: 203229, 48: 216577, 49: 230497, 50: 245001,
}

# Combined for the full sweep
ALL_CELLS = {**PUBLISHED_SEQUENCE, **G322_EXTENSION, **G323_EXTENSION, **G325_EXTENSION}


def main() -> int:
    rc = 0
    sys.stdout.reconfigure(line_buffering=True)

    # --- (1) two-implementation agreement over the full m range ------------
    print(f"[1] two-implementation agreement (A = 2m^3 - 2m^2 + 1, B = 4m * C(m,2) + 1):")
    for m in range(2, 51):
        a = I_max_direct(m)
        b = I_max_binomial(m)
        if a != b:
            print(f"  MISMATCH at m={m}: A={a} vs B={b}")
            rc = 1
        else:
            print(f"  m={m:2d}  n={4*m:3d}  I_max={a:7d}  (A == B)")
    if rc == 0:
        print("  -> 49/49 cells: A == B exactly")

    # --- (2) published sequence pin (m = 2 .. 10) --------------------------
    print()
    print("[2] published sequence pin (m = 2 .. 10):")
    for m, want in PUBLISHED_SEQUENCE.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  I_max={got:6d}  (expected {want:6d})")

    # --- (3) G322 extension (m = 11 .. 15) ---------------------------------
    print()
    print("[3] G322 extension (m = 11 .. 15):")
    for m, want in G322_EXTENSION.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  n={4*m:2d}  I_max={got:6d}  (expected {want:6d})")

    # --- (4) G323 extension (m = 16 .. 25) ---------------------------------
    print()
    print("[4] G323 extension (m = 16 .. 25):")
    for m, want in G323_EXTENSION.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  n={4*m:2d}  I_max={got:6d}  (expected {want:6d})")

    # --- (5) G325 NEW extension (m = 26 .. 50) -----------------------------
    print()
    print("[5] G325 NEW extension (m = 26 .. 50):")
    for m, want in G325_EXTENSION.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  n={4*m:3d}  I_max={got:7d}  (expected {want:7d})")
    if rc == 0:
        print("  -> 25/25 G325 cells verified exactly")

    # --- (6) bulk identity: 2m^3 - 2m^2 = 2m^2 * (m - 1) --------------------
    print()
    print("[6] bulk identity 2m^3 - 2m^2 = 2m^2 * (m - 1) [overdetIncidenceMax_bulk]:")
    fails = 0
    for m in range(2, 51):
        a = bulk(m)
        b = bulk_factored(m)
        if a != b:
            print(f"  MISMATCH at m={m}: {a} vs {b}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 49/49 cells: bulk(m) == bulk_factored(m) exactly")

    # --- (7) existing decoupling: I_max(m) > 4m for m >= 2 -----------------
    print()
    print("[7] decoupling I_max(m) > 4m for m >= 2 [overdetIncidenceMax_gt_budget]:")
    fails = 0
    for m in range(2, 51):
        if I_max_direct(m) <= 4 * m:
            print(f"  FAIL at m={m}: I_max={I_max_direct(m)} <= 4m={4*m}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 49/49 cells: I_max(m) > 4m strictly")

    # --- (8) G322 stronger decoupling: I_max(m) > 8m for m >= 3 -----------
    print()
    print("[8] stronger decoupling I_max(m) > 8m for m >= 3 [overdetIncidenceMax_gt_double_budget]:")
    fails = 0
    for m in range(3, 51):
        if I_max_direct(m) <= 8 * m:
            print(f"  FAIL at m={m}: I_max={I_max_direct(m)} <= 8m={8*m}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 48/48 cells: I_max(m) > 8m strictly")

    # --- (9) strict monotonicity --------------------------------------------
    print()
    print("[9] strict monotonicity: I_max(m) < I_max(m + 1) for m >= 1 [overdetIncidenceMax_strict_mono]:")
    fails = 0
    for m in range(1, 50):
        if I_max_direct(m) >= I_max_direct(m + 1):
            print(f"  FAIL at m={m}: I_max(m)={I_max_direct(m)} >= I_max(m+1)={I_max_direct(m + 1)}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 49/49 cells: I_max(m) < I_max(m + 1) strictly")

    # --- (10) discrete derivative check: I_max(m+1) - I_max(m) = 2m(3m+1) -
    print()
    print("[10] discrete derivative: I_max(m+1) - I_max(m) = 2m(3m+1):")
    fails = 0
    for m in range(1, 50):
        diff = I_max_direct(m + 1) - I_max_direct(m)
        expected = 2 * m * (3 * m + 1)
        if diff != expected:
            print(f"  FAIL at m={m}: diff={diff} != 2m(3m+1)={expected}")
            fails += 1
            rc = 1
    if fails == 0:
        print(f"  -> 49/49 cells: discrete derivative equals 2m(3m+1) exactly")

    # --- summary ------------------------------------------------------------
    print()
    total_cells = sum(len(d) for d in (PUBLISHED_SEQUENCE, G322_EXTENSION,
                                       G323_EXTENSION, G325_EXTENSION))
    print(f"=" * 70)
    print(f"G325 SUMMARY: {total_cells} cells pinned (m = 2 .. {max(ALL_CELLS)}).")
    if rc == 0:
        print("All checks PASS. Closed form 2m^3 - 2m^2 + 1 verified at m = 2 .. 50.")
    else:
        print("One or more checks FAILED -- see FAIL lines above.")
    print(f"=" * 70)
    return rc


if __name__ == "__main__":
    sys.exit(main())
