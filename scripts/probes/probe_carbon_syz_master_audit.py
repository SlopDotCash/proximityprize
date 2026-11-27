#!/usr/bin/env python3
"""Verify the exact arithmetic behind CarbonSYZMasterAuditAndF2Refutation.lean.

Checks (all pure integer arithmetic, < 0.1s, passes under `python3 -O`):
1. F2 & SYZ46-SYZ66 census chain refutation at the strip predecessor radius
   (357913940 / 2^30) on the first certified prize prime P_1 via the 4-head
   septic-core witness (313174699 < 357913940, bad count >= 2^30 + 1 >= 6).
2. Structural vacuity of StripMasterHypothesis / ' / '' at Ucard = n
   (2 * (n - k) + 1 <= 2 * (n - k) is False for every k <= n).
3. Symbolic 4-coset RegionSyzygyRealizable + StrictBandCores + non-SylvesterInjective
   witness at n = 2^30, k = 2^29, d = 2^28, t = 178956972 (exact strip threshold
   2d + t = 715827884) on BOTH certified prize primes P_1 and P_2, with imbalance
   iota = 2^27 = 134217728 >= 2.
"""

from __future__ import annotations

import sys


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"CHECK FAILED: {msg}")


def main() -> int:
    n = 1 << 30
    k = 1 << 29
    strip_numerator = 357913941
    strip_pred_num = strip_numerator - 1
    strip_threshold = n - strip_pred_num
    septic_err_num = 313174699

    # 1. F2 & census-chain refutation parameters on FirstPrimeSepticCores
    p1 = (1 << 30) * ((1 << 128) + 192) + 1
    p2 = (1 << 30) * (2 * (1 << 128) + 13) + 1
    check(p1 == 365375409332725729550921208179070755120141565953, "exact first prize prime P_1")
    check(p2 == 730750818665451459101842416358141509841924915201, "exact second prize prime P_2")
    check(p1 // (1 << 128) == (1 << 30), "P_1 / 2^128 = 2^30 (budget = 2^30)")
    check(p2 // (1 << 128) == (1 << 31), "P_2 / 2^128 = 2^31 (budget = 2^31)")
    check(strip_numerator * 3 == n - 1, "stripNumerator = (2^30 - 1) / 3")
    check(strip_pred_num == 357913940, "predecessor numerator = 357913940")
    check(strip_threshold == 715827884, "strip witness threshold = 715827884")
    check(septic_err_num < strip_pred_num, "septic core radius < strip predecessor radius")
    check((1 << 30) * (1 << 128) <= p1, "first prize prime satisfies 2^30 / P_1 <= 2^-128")
    check((1 << 30) * (1 << 128) <= p2, "second prize prime satisfies 2^30 / P_2 <= 2^-128")

    # Verify FirstPrimeSepticCores population counts
    s = 1 << 26
    cuts = {3: 11184809, 7: 44739243, 11: 11184810, 15: 33554432}
    ordinary_card = (
        12 * s
        + (s - cuts[3])
        + (s - cuts[11])
        + cuts[15]
        + (s - cuts[15])
    )
    special_card = s - cuts[7]
    roots_card = cuts[3] + cuts[7] + cuts[11]
    check(roots_card == s - 2, "roots.card = 2^26 - 2")
    check(ordinary_card + 4 * special_card == n + 1, "ordinary + 4 * special = 2^30 + 1")
    check(n + 1 >= 6, "over-budget bad count >= 6 (triggers syzygy regime)")

    # 2. StripMasterHypothesis vacuity at Ucard = n
    ucard = n
    lhs = 2 * (ucard - k) + 1
    rhs = 2 * (n - k)
    check(lhs == n + 1 and rhs == n and not (lhs <= rhs), "Ucard = n violates 2(Ucard-k)+1 <= 2(n-k)")

    # 3. Symbolic 4-coset witness at exact strip threshold on P_1 and P_2
    d = 1 << 28
    t = 178956972
    check(4 * d == n, "4 * d = 2^30")
    check(2 * d == k, "2 * d = 2^29")
    check(d >= 4, "d >= 4")
    check(2 * d + 1 <= 3 * t and t <= d - 1, "4-coset strip parameter range")
    check(2 * d + t == strip_threshold, "core size 2d + t = 715827884 (exact strip threshold)")
    # BandStack & StrictBandCores checks
    check(3 * d + t <= 2 * k, "domain disjointness 3d + t <= 2k")
    check(d + 1 + t <= k, "SYZ37 budget cap d + 1 + t <= k")
    check(2 * k + 1 <= 3 * d + 2 * t, "G172 interior slack 2k + 1 <= 3d + 2t")
    core_s = 2 * d + t
    check(4 * k + 1 <= 3 * core_s and 4 * core_s + 1 <= 6 * k, "StrictBandCores 2n/3 < s < 3n/4")
    # Imbalance and Sylvester cofactor budget
    delta1 = d
    imbalance = (3 * d) // 2 - delta1
    check(imbalance == (1 << 27) and imbalance >= 2, "imbalance = 2^27 = 134217728 >= 2")
    b_ac = k - 1 - (d + t)
    check(b_ac == 89478483 and b_ac >= 0, "Sylvester cofactor window budget >= 0 (constants fit)")

    # Check 4th-root-of-unity coset constants on both P_1 and P_2
    g1 = 303645430271030343624574566109998498685964493478
    g2 = 192152681249815148642741928588691886362054863855
    for idx, (p, g) in enumerate([(p1, g1), (p2, g2)], start=1):
        check(pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1, f"g_{idx} has exact order 2^30")
        omega = pow(g, d, p)
        check(len({1, omega, pow(omega, 2, p), pow(omega, 3, p)}) == 4, f"4 distinct coset roots mod P_{idx}")
        c0 = (omega - pow(omega, 2, p)) % p
        c1 = (pow(omega, 2, p) - 1) % p
        c2 = (1 - omega) % p
        check(c0 != 0 and c1 != 0 and c2 != 0, f"constant syzygy cofactors nonzero mod P_{idx}")
        check((c0 + c1 + c2) % p == 0, f"top X^d cancellation mod P_{idx}")
        check((-1 * c0 - omega * c1 - pow(omega, 2, p) * c2) % p == 0, f"constant term cancellation mod P_{idx}")

    print(
        "PASS: CarbonSYZ M1 master audit verified "
        f"(septic={septic_err_num}<{strip_pred_num}, 4-coset core={core_s}, iota={imbalance})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
