#!/usr/bin/env python3
"""Independent verification probe for EighthNearSaturatedPowers.

Verifies:
1. Near-saturated slack polytope over all 0 <= s <= 4 with optimal base head (3*z3 <= y3).
2. Constant-edge and quartic-direction-triple label caps for 1 <= q <= 5.
3. Complete arithmetic exhaustion of three power-slope triples (r = 0 on H, r = 1 on H^2),
   confirming only the 6 boundary triples in Families I and II survive.
4. Both branches (direct H and exact-saturated nonscalar-antipode quotient H^2) of the
   one-power companion degree floor B >= 7,479,697.
"""
from math import gcd

N = 2**30
K = 2**27
D = K - 1
E = 5 * K
RES = 20_607_410


def check_slack_polytope():
    max_pair_loss = 0
    min_msum_diff = 100
    max_msum_diff = -100
    max_z3 = 0
    for s in range(5):
        for x0 in range(s + 1):
            for x4 in range(s + 1):
                for y3 in range(2 * s + 1):
                    for z3 in range(2 * s + 1):
                        if y3 + z3 + 2 * x4 + 2 * x0 > 2 * s:
                            continue
                        if 3 * z3 > y3:
                            continue
                        pair_loss = 2 * s - 2 * x0 - y3 + 2 * z3 - 2 * x4
                        msum_hi = s - x0 - y3 - 2 * x4
                        msum_lo = -((2 * s + z3 - 2 * x0) // 2)
                        max_pair_loss = max(max_pair_loss, pair_loss)
                        min_msum_diff = min(min_msum_diff, msum_lo)
                        max_msum_diff = max(max_msum_diff, msum_hi)
                        max_z3 = max(max_z3, z3)
    assert max_pair_loss == 8, max_pair_loss
    assert min_msum_diff == -5, min_msum_diff
    assert max_msum_diff == 4, max_msum_diff
    assert max_z3 == 2, max_z3
    print(f"[PASS] Slack polytope: max_pair_loss={max_pair_loss}, msum-D in [{min_msum_diff}, {max_msum_diff}], max_z3={max_z3}")


def check_constant_and_quartic_caps():
    cap_q2 = 3 * (1 + E) + (1 + E // 2) - (4 * K - 5) + RES
    cap_q1 = 4 * (1 + E) - 2 * (4 * K - 1) + RES
    cap_quartic = 3 * (N // 4) + (2 * (N - (3 * K - 5)) - (2 * D - 10) + 12) + RES
    assert cap_q2 == 1_832_546_747 < 2 * N, cap_q2
    assert cap_q1 == 1_631_220_152 < 2 * N, cap_q1
    assert cap_quartic == 1_899_655_636 < 2 * N, cap_quartic
    print(f"[PASS] Caps: q>=2 const={cap_q2:,}, q=1 const={cap_q1:,}, quartic={cap_quartic:,} (all << {2*N:,})")


def is_pow2(x: int) -> bool:
    return x > 0 and (x & (x - 1)) == 0


def check_power_triples():
    # Cutoffs
    assert 46341 * 46340 <= 2 * (N - 1) < 46342 * 46341
    assert 32768 * 32767 <= 2 * (N // 2 - 1) < 32769 * 32768

    # Odd (r = 0) triples: a >= b >= c >= 1, a <= D, D-5 <= a+b+c <= D+4, not all even
    odd_sols = set()
    for a_cand in set(
        [pw - t for pw in (2**26, 2**27) for t in range(1, 5)]
        + [pw + t for pw in (2**26, 2**27) for t in range(1, 5)]
    ):
        if not (1 <= a_cand <= D and a_cand % 2 == 1):
            continue
        for pw_b in (2**26, 2**27):
            for b in (pw_b - a_cand, a_cand - pw_b):
                if not (1 <= b <= a_cand):
                    continue
                if b == a_cand - pw_b and b > 4:
                    continue
                for S in range(D - 5, D + 5):
                    c = S - a_cand - b
                    if not (1 <= c <= b):
                        continue
                    ok_ac = is_pow2(a_cand + c) or (c <= 4 and is_pow2(a_cand - c))
                    if ok_ac:
                        odd_sols.add((a_cand, b, c))

    expected_odd = {
        (2**26 + 1, 2**26 - 1, 1),
        (2**26 + 3, 2**26 - 3, 3),
        (2**27 - 1, 1, 1),
        (2**27 - 3, 3, 3),
    }
    assert odd_sols == expected_odd, odd_sols

    # Even (r = 1) triples: (a,b,c) = 2*(a',b',c'), not all a',b',c' even
    even_sols = set()
    for a_p in set(
        [pw - t for pw in (2**25, 2**26) for t in range(1, 3)]
        + [pw + t for pw in (2**25, 2**26) for t in range(1, 3)]
    ):
        if not (1 <= 2 * a_p <= D and a_p % 2 == 1):
            continue
        for pw_b in (2**25, 2**26):
            for b_p in (pw_b - a_p, a_p - pw_b):
                if not (1 <= b_p <= a_p):
                    continue
                if b_p == a_p - pw_b and b_p > 2:
                    continue
                for S in range(D - 5, D + 5):
                    if S % 2 != 0:
                        continue
                    c_p = S // 2 - a_p - b_p
                    if not (1 <= c_p <= b_p):
                        continue
                    ok_ac = is_pow2(a_p + c_p) or (c_p <= 2 and is_pow2(a_p - c_p))
                    if ok_ac:
                        even_sols.add((2 * a_p, 2 * b_p, 2 * c_p))

    expected_even = {
        (2**26 + 2, 2**26 - 2, 2),
        (2**27 - 2, 2, 2),
    }
    assert even_sols == expected_even, even_sols
    print(f"[PASS] Exact 6 surviving boundary triples: {sorted(odd_sols | even_sols)}")


def check_companion_floors():
    # Branch A: direct on H
    B_direct = next(
        B for B in range(7_479_680, 7_479_720)
        if (D - 13 - B) * (D - 14 - B) <= 2 * B * (N - 1)
    )
    assert B_direct == 7_479_697, B_direct
    assert (D - 13 - (B_direct - 1)) * (D - 14 - (B_direct - 1)) > 2 * (B_direct - 1) * (N - 1)

    # Branch B: exact-saturated H^2 quotient
    D2 = 2**26 - 1
    N2 = 2**29
    Bp = next(
        B for B in range(3_739_840, 3_739_860)
        if (D2 - B) * (D2 - 1 - B) <= 2 * B * (N2 - 1)
    )
    assert Bp == 3_739_849, Bp
    assert 2 * Bp - 1 == 7_479_697
    print(f"[PASS] Companion floor: direct B >= {B_direct:,}, H^2 quotient B' >= {Bp:,} => B >= {2*Bp - 1:,}")


if __name__ == "__main__":
    check_slack_polytope()
    check_constant_and_quartic_caps()
    check_power_triples()
    check_companion_floors()
    print("ALL CHECKS PASSED")
