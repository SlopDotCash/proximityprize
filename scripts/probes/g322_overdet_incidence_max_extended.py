#!/usr/bin/env python3
"""G322 exact probe: extended overdet far-line incidence MAX closed form.

Extends the published sequence 9, 37, 97, 201, 361, 589, 897, 1297, 1801
(m = 2 .. 10, n = 8 .. 40) of the over-determined far-line incidence MAX

    I_max(n) = n^3/32 - n^2/8 + 1   =   2*m^3 - 2*m^2 + 1   (with n = 4*m)

(pinned in ArkLib/Data/CodingTheory/ProximityGap/OverdetIncidenceMaxClosedForm.lean)
to cover m = 2 .. 20, with TWO independent implementations:

  (A) direct cubic form:       2 * m^3 - 2 * m^2 + 1
  (B) alternative binomial:    4 * m * (m * (m - 1) // 2) + 1
                              (= n * C(m, 2) + 1, since m*(m-1) is even for m >= 1)

The two implementations MUST agree at every m. We also verify:

  - the existing Lean pin m = 2 .. 10 (sequence 9, 37, ..., 1801),
  - the extended m = 11 .. 20 values (2421, 3169, ..., 15201),
  - the "bulk" identity 2m^3 - 2m^2 = 2m^2 * (m - 1) (used by `overdetIncidenceMax_bulk`),
  - the existing decoupling inequality `I_max(m) > 4*m` for m >= 2
    (= `overdetIncidenceMax_gt_budget`),
  - the STRONGER decoupling inequality `I_max(m) > 8*m` for m >= 3
    (overdet MAX exceeds DOUBLE the budget n = 4m),
  - strict monotonicity: `I_max(m) < I_max(m + 1)` for m >= 1
    (difference = 2m * (3m + 1), positive for m >= 1).

All arithmetic is exact Python `int` -- no `float`, no `Fraction` needed, no
`sympy`/`numpy`/`scipy`. The only division in implementation (B) is `m*(m-1)//2`,
which is exact because `m*(m-1)` is always even for `m >= 1` (one of `m`, `m-1`
is even); we `assert (m*(m-1)) % 2 == 0` for sanity at every m.

This is a (P)/(C) brick: the closed form is a (P) Lean kernel pinned at the
published cells, and the probe carries an exact integer cross-check (C) that
extends the pin to m = 11 .. 20.
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

# Extended sequence proposed for pinning in the G322 extension (m = 11 .. 20)
EXTENDED_SEQUENCE = {
    11: 2421, 12: 3169, 13: 4057, 14: 5097, 15: 6301,
    16: 7681, 17: 9249, 18: 11017, 19: 12997, 20: 15201,
}

# Further extended sequence for the G323 brick (m = 21 .. 25)
FURTHER_EXTENDED_SEQUENCE = {
    21: 17641, 22: 20329, 23: 23277, 24: 26497, 25: 30001,
}

# Combined for the full sweep
ALL_CELLS = {**PUBLISHED_SEQUENCE, **EXTENDED_SEQUENCE, **FURTHER_EXTENDED_SEQUENCE}


def main() -> int:
    rc = 0

    # --- (1) two-implementation agreement over the full m range ------------
    print("[1] two-implementation agreement (A = 2m^3 - 2m^2 + 1, B = 4m * C(m,2) + 1):")
    for m in range(2, 26):
        a = I_max_direct(m)
        b = I_max_binomial(m)
        if a != b:
            print(f"  MISMATCH at m={m}: A={a} vs B={b}")
            rc = 1
        else:
            print(f"  m={m:2d}  n={4*m:2d}  I_max={a:6d}  (A == B)")
    if rc == 0:
        print("  -> 24/24 cells: A == B exactly")

    # --- (2) published sequence pin (m = 2 .. 10) --------------------------
    print()
    print("[2] published sequence pin (m = 2 .. 10):")
    for m, want in PUBLISHED_SEQUENCE.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  I_max={got:6d}  (expected {want:6d})")

    # --- (3) extended sequence (m = 11 .. 20) ------------------------------
    print()
    print("[3] extended sequence (m = 11 .. 20):")
    for m, want in EXTENDED_SEQUENCE.items():
        got = I_max_direct(m)
        ok = "OK " if got == want else "BAD"
        if got != want:
            rc = 1
        print(f"  [{ok}] m={m:2d}  n={4*m:2d}  I_max={got:6d}  (expected {want:6d})")

    # --- (4) bulk identity: 2m^3 - 2m^2 = 2m^2 * (m-1) ----------------------
    print()
    print("[4] bulk identity 2m^3 - 2m^2 = 2m^2 * (m - 1):")
    for m in range(2, 26):
        a = bulk(m)
        b = bulk_factored(m)
        ok = "OK " if a == b else "BAD"
        if a != b:
            rc = 1
        print(f"  [{ok}] m={m:2d}  bulk={a:6d}  bulk_factored={b:6d}")
    if rc == 0:
        print("  -> 24/24 cells: bulk identity holds")

    # --- (5) existing decoupling inequality: I_max(m) > 4*m for m >= 2 -----
    print()
    print("[5] existing decoupling: I_max(m) > 4*m (= `overdetIncidenceMax_gt_budget`):")
    for m in range(2, 26):
        v = I_max_direct(m)
        b = 4 * m
        ok = "OK " if v > b else "BAD"
        if v <= b:
            rc = 1
        print(f"  [{ok}] m={m:2d}  I_max={v:6d} > 4m={b:4d}")

    # --- (6) STRONGER decoupling: I_max(m) > 8*m for m >= 3 ----------------
    # (overdet MAX exceeds DOUBLE the budget n = 4m; the binding witness s*
    # is therefore not just over budget, it's over double budget)
    print()
    print("[6] STRONGER decoupling: I_max(m) > 8*m for m >= 3:")
    for m in range(3, 26):
        v = I_max_direct(m)
        b = 8 * m
        ok = "OK " if v > b else "BAD"
        if v <= b:
            rc = 1
        print(f"  [{ok}] m={m:2d}  I_max={v:6d} > 8m={b:4d}")
    if rc == 0:
        print("  -> 23/23 cells (m=3..25): overdet MAX > double budget")

    # --- (7) strict monotonicity: I_max(m) < I_max(m + 1) for m >= 1 -------
    # (the discrete derivative is 2m*(3m+1), positive for m >= 1)
    print()
    print("[7] strict monotonicity: I_max(m) < I_max(m+1) for m >= 1:")
    for m in range(1, 25):
        v = I_max_direct(m)
        vnext = I_max_direct(m + 1)
        diff = vnext - v
        expected_diff = 2 * m * (3 * m + 1)
        ok = "OK " if v < vnext and diff == expected_diff else "BAD"
        if v >= vnext or diff != expected_diff:
            rc = 1
        print(
            f"  [{ok}] m={m:2d}  I_max(m)={v:6d}  I_max(m+1)={vnext:6d}  "
            f"diff={diff:6d}  (= 2m(3m+1)={expected_diff})"
        )
    if rc == 0:
        print("  -> 24/24 cells: strictly increasing; diff = 2m(3m+1) verified")

    # --- summary -----------------------------------------------------------
    print()
    if rc == 0:
        print("=" * 70)
        print("ALL CHECKS PASSED.")
        print(f"Closed form I_max(m) = 2m^3 - 2m^2 + 1 verified at m = 2 .. 25")
        print(f"Alternative form I_max(m) = 4m * C(m, 2) + 1 verified (m = 2 .. 25)")
        print(f"Existing decoupling I_max(m) > 4m verified (m = 2 .. 25)")
        print(f"Stronger decoupling I_max(m) > 8m verified (m = 3 .. 25)")
        print(f"Strict monotonicity I_max(m) < I_max(m+1) verified (m = 1 .. 24)")
        print(f"Bulk identity 2m^3 - 2m^2 = 2m^2 * (m-1) verified (m = 2 .. 25)")
        print("=" * 70)
    return rc


if __name__ == "__main__":
    sys.exit(main())
