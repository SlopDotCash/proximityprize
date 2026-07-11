#!/usr/bin/env python3
"""Exact audit of normalized subset-discrepancy transition ratios on H8 < F_17.

This tests the proposed integrality-jump route for the BGK one-unit Wick target.
For Z_r = sum_y (q a_r(y)-C(n,r))^2 / C(n,r)^2, the normalized transition is
    c_r = n Z_{r+1} / Z_r.
If these ratios were integers, a strict c_r < 2r+1 estimate could round down by
one.  The genuine subgroup H8 refutes that property: five of its six ratios are
nonintegral.
"""

from fractions import Fraction
from itertools import combinations

Q = 17
H8 = (1, 2, 4, 8, 9, 13, 15, 16)


def normalized_subset_deviation(r: int) -> Fraction:
    counts = [0] * Q
    for subset in combinations(H8, r):
        counts[sum(subset) % Q] += 1
    total = sum(counts)
    energy = sum((Q * count - total) ** 2 for count in counts)
    return Fraction(energy, total**2)


def main() -> None:
    deviations = [normalized_subset_deviation(r) for r in range(1, 8)]
    ratios = [Fraction(len(H8)) * deviations[r] / deviations[r - 1]
              for r in range(1, 7)]

    expected_deviations = [
        Fraction(153, 8), Fraction(51, 14), Fraction(561, 392),
        Fraction(204, 175), Fraction(561, 392), Fraction(51, 14),
        Fraction(153, 8),
    ]
    expected_ratios = [
        Fraction(32, 21), Fraction(22, 7), Fraction(1792, 275),
        Fraction(275, 28), Fraction(224, 11), Fraction(42, 1),
    ]
    assert deviations == expected_deviations
    assert ratios == expected_ratios
    assert sum(r.denominator != 1 for r in ratios) == 5

    print("H8 normalized deviations:", ", ".join(map(str, deviations)))
    print("H8 normalized transitions:", ", ".join(map(str, ratios)))
    print("VERDICT: five of six genuine subgroup ratios are nonintegral;")
    print("strict Wick bounds do not round down without extra production divisibility.")


if __name__ == "__main__":
    main()
