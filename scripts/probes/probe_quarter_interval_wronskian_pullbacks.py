#!/usr/bin/env python3
"""Independent verification of the Kummer determinant height floor and uniform
Wronskian pullback exclusions across [447,392,428, 480,946,858]."""

from fractions import Fraction
from math import ceil


def verify_kummer_floors():
    n = 2 ** 30
    for q, expected_H in [(1, 128), (2, 108), (2 ** 21, 4), (2 ** 23, 3)]:
        H = 1
        while 4 * q * H ** 4 < n:
            H += 1
        assert H == expected_H, f"q={q}: got {H}, expected {expected_H}"
    print("Kummer determinant height floors verified: q<=2 -> H>=108, q<=2^21 -> H>=4, q<=2^23 -> H>=3.")


def verify_interval_floors():
    n = 2 ** 30
    D = 2 ** 28 - 2

    # 1. Beat 480,946,859 (S >= 603,979,777)
    S1 = 603_979_777
    slope1 = S1 - Fraction(2, 5) * n
    loss1 = Fraction(3 * D - S1, 2)
    assert slope1 - Fraction(3, 2) * loss1 > 0
    assert ceil(slope1 / 14) == 12_463_075
    f2_1 = Fraction(S1 ** 2, 6 * D) + Fraction(S1, 2)
    # r <= 21, w = 2:
    assert 2 * ceil((f2_1 - Fraction(2, 5) * n) / 14) == 14_140_798 > 12_463_075
    # r = 22, w = 2 (using h=4, k=2, M=14):
    assert f2_1 > Fraction(3, 7) * n + 13 * (2 ** 22)
    # r = 22, w >= 3:
    assert 3 * (2 ** 22) == 12_582_912 > 12_463_075
    # r >= 23, w >= 2:
    assert 2 * (2 ** 23) == 16_777_216 > 12_463_075

    # 2. Unrestricted through 469,762,048 (S >= 671,088,641)
    S2 = 671_088_641
    slope2 = S2 - Fraction(1, 2) * n
    loss2 = Fraction(3 * D - S2, 2)
    assert slope2 - Fraction(3, 2) * loss2 > 0
    assert ceil(slope2 / 7) == 19_173_962
    f2_2 = Fraction(S2 ** 2, 6 * D) + Fraction(S2, 2)
    assert 2 * ceil((f2_2 - Fraction(1, 2) * n) / 7) == 22_369_624 > 19_173_962
    assert 2 * (2 ** 24) == 33_554_432 > 19_173_962

    # 3. Characteristic headroom
    p1 = 365375409332725729550921208179070755120141565953
    p2 = 730750818665451459101842416358141509841924915201
    assert 6 * n * D < 2 ** 61 < p1 < p2
    print("All uniform Wronskian inner-degree floors across [447,392,428, 480,946,858] verified:")
    print("  S >= 603,979,777 (all 3-head attacks beating 480,946,859): non-dihedral deg T >= 12,463,075")
    print("  S >= 671,088,641 (all unrestricted attacks <= 469,762,048): non-dihedral deg T >= 19,173,962")


if __name__ == "__main__":
    verify_kummer_floors()
    verify_interval_floors()
