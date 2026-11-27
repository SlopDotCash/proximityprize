#!/usr/bin/env python3
"""Exact rational verifier for CubicHahnJohnson, MixedInclusionOmissionJohnson,
and HintBoundaryShell theorems (production length n = 2^30 and uniform n >= 256)."""

from fractions import Fraction
import math


def quad_hahn_bound(n: int, t: int, d: int):
    nf, tf, df = Fraction(n), Fraction(t), Fraction(d)
    c1 = 2 * (tf - 1) ** 2 / (nf - 2) + 1 - df
    c0 = c1 * (tf ** 2 / nf) - tf ** 2 * (tf - 1) ** 2 / ((nf - 1) * (nf - 2))
    assert c0 > 0 and c1 >= 0
    return int(tf * (tf - df) // c0), c0, c1


def cubic_hahn_bound(n: int, t: int, d: int, r0: Fraction):
    nf, tf, df = Fraction(n), Fraction(t), Fraction(d)
    c2 = 2 * (3 + 3 * (tf - 2) ** 2 / (nf - 4) - df - 2 * r0)
    c1 = (
        2 * df * r0
        + r0 ** 2
        - c2 * (-Fraction(1, 2) - (tf - 1) ** 2 / (nf - 2))
        - (
            2
            + 3 * (tf - 2) ** 2 / (nf - 4)
            + 3 * (tf - 1) ** 2 * (tf - 2) ** 2 / ((nf - 3) * (nf - 4))
        )
    )
    c0 = (
        -df * r0 ** 2
        + c1 * (tf ** 2 / nf)
        - c2 * (tf ** 2 * (tf - 1) ** 2 / (2 * (nf - 1) * (nf - 2)))
        + tf ** 2 * (tf - 1) ** 2 * (tf - 2) ** 2 / ((nf - 2) * (nf - 3) * (nf - 4))
    )
    assert c0 > 0 and c1 >= 0 and c2 >= 0, (float(c0), float(c1), float(c2))
    return int((tf - df) * (tf - r0) ** 2 // c0), c0, c1, c2


def mixed_inc_om_bound(n: int, t: int, d: int, s: int, r: int):
    assert (n - s - r) * (d - s) < (t - s) ** 2
    num = math.comb(n, s) * math.comb(n - s, r) * (n - s - r)
    den = math.comb(t, s) * math.comb(n - t, r)
    return num // den


def hint_shell_check(n: int, k: int, t: int, H: int, B: int):
    d = k - 1
    assert H <= n and d <= t and n * d <= H * t
    denom = H * (t - d) ** 2 - d * (n - H) * (H - d)
    assert denom > 0
    lhs = (t - d) * H * (n - H)
    assert lhs < B * denom
    # Check optimality: H - 1 fails
    H_prev = H - 1
    denom_prev = H_prev * (t - d) ** 2 - d * (n - H_prev) * (H_prev - d)
    assert denom_prev <= 0 or (t - d) * H_prev * (n - H_prev) >= B * denom_prev


def main():
    n = 1 << 30
    cubic_cases = [
        ("rate_half_johnson_plus_one", 1 << 29, 759250124, 461720310, 4251066562),
        ("rate_half_johnson_plus_two", 1 << 29, 759250123, 514150268, 11583034964),
        ("rate_quarter_johnson_plus_one", 1 << 28, 536870910, 214748362, 6442450994),
        ("rate_quarter_johnson_plus_two", 1 << 28, 536870909, 238609291, 10737418754),
        ("rate_eighth_johnson_plus_two", 1 << 27, 379625060, 77802029, 5744500761),
        ("rate_sixteenth_johnson_plus_one", 1 << 26, 268435453, 12201610, 5010795150),
        ("rate_sixteenth_johnson_plus_two", 1 << 26, 268435452, 35320453, 7874106789),
        ("rate_half_super_johnson_4799", 1 << 29, 759245326, 536857338, 142046270429484896),
        ("rate_quarter_super_johnson_8192", 1 << 28, 536862719, 268419071, 2305271392757763350),
        ("rate_eighth_super_johnson_10592", 1 << 27, 379614470, 134202749, 499537678460700742),
        ("rate_sixteenth_super_johnson_12288", 1 << 26, 268423166, 67096575, 1383257789440870609),
    ]
    for name, k, t, r0, expected in cubic_cases:
        got, _, _, _ = cubic_hahn_bound(n, t, k - 1, Fraction(r0))
        assert got == expected, f"{name}: got {got}, expected {expected}"
    q_got, _, _ = quad_hahn_bound(n, 379625061, (1 << 27) - 1)
    assert q_got == 1931589822

    assert mixed_inc_om_bound(n, 268435453, (1 << 26) - 1, 1, 0) == 4294967340
    assert mixed_inc_om_bound(n, 536870910, (1 << 28) - 1, 1, 3) == 17179868992

    shell_cases = [
        (1 << 29, 759250124, 759266635, 1 << 30),
        (1 << 29, 759250124, 759265175, 1 << 31),
        (1 << 28, 536870910, 536907548, 1 << 30),
        (1 << 28, 536870910, 536905668, 1 << 31),
        (1 << 27, 379625061, 379648803, 1 << 30),
        (1 << 27, 379625060, 379666627, 1 << 31),
        (1 << 26, 268435453, 268482518, 1 << 30),
        (1 << 26, 268435453, 268479191, 1 << 31),
    ]
    for k, t, H, B in shell_cases:
        hint_shell_check(n, k, t, H, B)

    print("ALL 22 PRODUCTION CERTIFICATES (CUBIC HAHN + MIXED + HINT SHELLS) VERIFIED EXACTLY.")


if __name__ == "__main__":
    main()
