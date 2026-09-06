#!/usr/bin/env python3
"""G324 reproducible probe: the depth-4 dyadic wall floor under the naive cap.

Extends G316 (`_G316DyadicWallFloorDepth3.lean`) from depth-3 partitions
{1, 2, 3} to depth-4 partitions {1, 2, 3, 4} under the NAIVE cap extension:
the class count cap from G206 is now a+b+c+d <= m, k values are in
{1, 2, 3, 4}, and the partition constraint is a+2b+3c+4d = n-1 = 2m-1.

Maximizing sum k^2 = a + 4b + 9c + 16d under these constraints:

  efficiency(i) = i^2 / i = i, so 4s dominate (16/4 = 4 efficiency vs. 9/3 = 3
  for 3s, 4/2 = 2 for 2s, 1/1 = 1 for 1s). Use as many 4s as possible:
  a_4 = floor((2m-1) / 4), remainder r = (2m-1) mod 4 in {1, 3} (since 2m-1
  is always odd). Both r=1 (use one 1, value 1) and r=3 (use one 3, value 9)
  give the same total: 16 * floor((2m-1)/4) + r^2 = 8m - 7 for all m >= 2.

  The count constraint floor((2m-1)/4) + 1 <= m is satisfied for all m >= 2.

So the closed form is the UNIVERSAL

    depth-4 floor = 8m - 7        (for all m >= 2)

This equals G316's depth-3 floor at m = 2 and is strictly above it for
m >= 3 (gap = 2m - 2, or 2m - 4 when m mod 3 == 2). It is strictly above
G215's depth-2 floor 4m-3 for m >= 2 (gap = 4m - 4).

The pattern across depths:

  depth 2: 4m - 3   (= 2*2*(m-1) + 1)
  depth 3: 6m - 5   (= 2*3*(m-1) + 1)  -- or 6m-3 at m mod 3 == 2
  depth 4: 8m - 7   (= 2*4*(m-1) + 1)  -- UNIVERSAL (no m mod 4 split needed)

THINNESS-ESSENTIAL. As with G316, this is a numerical sanity check of the
NAIVE cap extension: the G206 class-count cap a+b+c+d <= m is held fixed
while the k-value range is extended from {1, 2, 3} to {1, 2, 3, 4}. The
Lean side does NOT claim that the cap and partition machinery extend to
depth-4 unchanged; this file only states the integer-arithmetic closed
form. The kernel-side upgrade of the dyadic involution (G206) and the
partition engine (G209) to depth-4 partitions is open work; in particular
the cap a+b+c+d <= m might not extend to depth-4 unchanged. A kernel-side
refutation of the naive extension at some specific (n, m) would be a more
interesting result than a clean pin.

SCOPE / no prize claim. As with G215/G316, this sharpens a wall-floor
lower bound at the depth-4 partition level. It does NOT bound the signed
simultaneous cyclotomic-class covariance, does NOT bound higher-depth
partitions, and does NOT close the prize. CORE remains OPEN / ON-BGK.

KERNEL SCOPE. The Lean side pins the closed form at specific m values via
`decide` (a kernel-blessed tactic for `ℕ`/`ℤ` literal equality -- NOT
`native_decide`/`bv_decide`, which the campaign's
`scripts/forbidden_tokens.py` precheck rejects as kernel-bypassing). The
closed form is checked here only for 198 values, m = 2 through 199, using
exact integer enumeration. This finite replay is not a proof for all m.
The formula derivation above and any universal Lean proof require separate
justification; no universal kernel verification is claimed by this probe.
"""
from __future__ import annotations


def brute_force_depth4(m: int) -> tuple[int, tuple[int, int, int, int]]:
    """Brute-force max of a + 4b + 9c + 16d over (a,b,c,d) with
    a+2b+3c+4d = 2m-1, a+b+c+d <= m, all >= 0.

    Loops over d, c, b and COMPUTES a = (2m-1) - 2b - 3c - 4d directly
    (a is uniquely determined by the sum constraint; no a loop needed).
    Uses the per-d c_max bound (target - 4*d) // 3 and per-(c,d) b_max
    bound (m - c - d) AND (target - 3c - 4d) // 2 (intersection of the
    count and sum constraints). Uses three nested bounded loops (O(m^3) worst-case
    instead of the four-loop O(m^4) enumeration). Returns (max_value, witness).
    """
    n = 2 * m
    target = n - 1
    d_max = target // 4
    best = -1
    best_partition = None
    for d in range(0, d_max + 1):
        # c_max depends on d: 3c <= target - 4d, so c <= (target - 4d) // 3.
        c_max = (target - 4 * d) // 3
        for c in range(0, c_max + 1):
            # b_max: count constraint b <= m - c - d; sum constraint
            # 2b <= target - 3c - 4d, so b <= (target - 3c - 4d) // 2.
            b_max = min(m - c - d, (target - 3 * c - 4 * d) // 2)
            if b_max < 0:
                continue
            for b in range(0, b_max + 1):
                # a is uniquely determined by the sum constraint.
                a = target - 2 * b - 3 * c - 4 * d
                if a < 0:
                    continue
                # a + b + c + d <= m is the only remaining constraint
                # (a >= 0, b >= 0, c >= 0, d >= 0 already ensured above).
                if a + b + c + d > m:
                    continue
                val = a + 4 * b + 9 * c + 16 * d
                if val > best:
                    best = val
                    best_partition = (a, b, c, d)
    return best, best_partition


def closed_form_depth4(m: int) -> int:
    """Closed form: 8m - 7 (universal for m >= 2)."""
    return 8 * m - 7


def closed_form_depth3(m: int) -> int:
    """G316 closed form: 6m - 5 main / 6m - 3 at m mod 3 == 2."""
    return 6 * m - 5 + (2 if m % 3 == 2 else 0)


def depth2_floor(m: int) -> int:
    """G215 depth-2 floor: 4m - 3."""
    return 4 * m - 3


def main() -> int:
    rc = 0
    rows = []
    for m in range(2, 200):
        n = 2 * m
        bf, bf_part = brute_force_depth4(m)
        cf = closed_form_depth4(m)
        d2 = depth2_floor(m)
        d3 = closed_form_depth3(m)
        if bf != cf:
            print(f"MISMATCH m={m} n={n}: brute={bf} ({bf_part}) vs closed={cf}")
            rc = 1
        # depth-4 >= depth-3 for all m (equality at m=2 since 4 > n-1=3 forbids any 4s)
        if cf < d3:
            print(f"DEPTH4-BELOW-DEPTH3 m={m} n={n}: depth-4 {cf} < depth-3 {d3}")
            rc = 1
        # depth-4 > depth-3 STRICTLY for m >= 3 (the regime where 4s can appear)
        if m >= 3 and cf == d3:
            print(f"DEPTH4-NOT-STRICT-ABOVE-DEPTH3 m={m} n={n}: depth-4 {cf} == depth-3 {d3}")
            rc = 1
        if cf <= d2:
            print(f"DEPTH4-NOT-ABOVE-DEPTH2 m={m} n={n}: depth-4 {cf} <= depth-2 {d2}")
            rc = 1
        rows.append((n, m, d2, d3, bf, cf, bf - d2, bf - d3, bf_part, m % 4, m % 3))

    if rc == 0:
        print("G324 depth-4 dyadic wall floor (naive cap): PASS for n=2m, m in [2, 199].")
        print("  depth-4 floor = 8m - 7   (checked for m in [2, 199])")
        print("  equal to G316's depth-3 floor at m=2; strictly above it for checked m >= 3.")
        print("  strictly above G215's depth-2 floor of 4m-3 at every m >= 2.")
        print()
        print(f"  {'n':>4} {'m':>4} {'m%4':>4} {'m%3':>4} {'depth2':>7} {'depth3':>7} "
              f"{'depth4':>7} {'brute':>7} {'gap_d2':>7} {'gap_d3':>7}  witness (a,b,c,d)")
        for n, m, d2, d3, d4, bf, gd2, gd3, part, m4, m3 in rows:
            if n in (4, 6, 8, 10, 12, 16, 20, 24, 28, 32, 48, 64, 96, 128, 192, 256, 320, 384, 398):
                print(f"  {n:>4} {m:>4} {m4:>4} {m3:>4} {d2:>7} {d3:>7} {d4:>7} {bf:>7} "
                      f"{gd2:>7} {gd3:>7}  {part}")
    return rc


if __name__ == "__main__":
    import sys
    sys.exit(main())
