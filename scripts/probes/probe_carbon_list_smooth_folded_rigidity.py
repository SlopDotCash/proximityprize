#!/usr/bin/env python3
"""Exact arithmetic & algebraic verifier for CarbonListSmoothFoldedRigidity.lean (<0.2s, -O safe)."""
import math


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def verify_sixteenth_identity() -> None:
    for k in [4, 8, 16, 67108864]:
        for s in [1, 2, 3]:
            n = 16 * k
            d = k - 1
            t = 4 * k - 2 - s
            lhs = (t - s) ** 2
            rhs = (n - s) * (d - s) + s * k + (3 * s + 4) * (s + 1)
            check(lhs == rhs, f"Identity failed at k={k}, s={s}: {lhs} != {rhs}")
            check((n - s) * (d - s) < (t - s) ** 2, "Strict inequality failed")


def verify_production_mixed_bounds() -> None:
    n = 1073741824
    cases = [
        ("eighth_j2", 134217728, 694116764, 379625060, 2, 0, 8589934703),
        ("eighth_j3", 134217728, 694116765, 379625059, 3, 2, 58139264338),
        ("sixteenth_j2", 67108864, 805306372, 268435452, 2, 0, 17179869712),
        ("sixteenth_j3", 67108864, 805306373, 268435451, 3, 0, 68719480960),
    ]
    for name, k, e, t, s, r, B in cases:
        check(e + t == n, f"e + t != n for {name}")
        check((n - s - r) * (k - 1 - s) < (t - s) ** 2, f"Not Johnson-safe for {name}")
        num = math.comb(n, s) * math.comb(n - s, r) * (n - s - r)
        den = math.comb(t, s) * math.comb(n - t, r)
        check(num // den == B, f"Exact floor mismatch for {name}: {num // den} != {B}")
        check(num < (B + 1) * den, f"Budget inequality failed for {name}")


def verify_star_and_triangle_constants() -> None:
    n = 1073741824
    # Rate 1/2 J+1: star cap <= 2, triangle degree >= 130266726
    k2, t2 = 536870912, 759250124
    check((n - (k2 - 1)) < 3 * (t2 - (k2 - 1)), "Rate 1/2 star cap 2 failed")
    check(3 * t2 - 2 * (k2 - 1) - n == 130266726, "Rate 1/2 min pencil degree mismatch")
    # Rate 1/4 J+1: star cap <= 3
    k4, t4 = 268435456, 536870910
    check((n - (k4 - 1)) < 4 * (t4 - (k4 - 1)), "Rate 1/4 star cap 3 failed")
    # Rate 1/8 J+1: star cap <= 3 (so every saturated K_4 forces a 3-split pencil!)
    k8, t8 = 134217728, 379625061
    check((n - (k8 - 1)) < 4 * (t8 - (k8 - 1)), "Rate 1/8 star cap 3 failed")


def main() -> None:
    verify_sixteenth_identity()
    verify_production_mixed_bounds()
    verify_star_and_triangle_constants()
    print("ALL CarbonListSmoothFoldedRigidity checks passed!")


if __name__ == "__main__":
    main()
