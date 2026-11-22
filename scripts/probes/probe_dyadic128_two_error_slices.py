#!/usr/bin/env python3
"""Verify the local penalty certificate for the 237-bit length-128 RS list.

All dictionary keys are actual elements of the sponsor-instance prime field.
Rotating the fixed pair reduces it to (1,z^d); interchanging its two endpoints
replaces d by -d. The antipodal separation 64 is discarded by the proof.
"""

from collections import Counter
from itertools import combinations
from math import comb

P = 126205134105047729256068842055334737587878534445324289139206048206460929
G = 50329493603183882829305332600678170099788838530533491465177960535524808
N = 128
BUDGET = P // 2**128


def penalty(number_of_alternatives):
    # These charges subtract from a starting weight of three sixths.
    return 0 if number_of_alternatives <= 1 else 1 if number_of_alternatives == 2 else 3


def fixed_pair(points, u, v):
    """Upper bound the total penalty for every scale, including unreached scales."""
    ratios = [(x - u) * pow((x - v) % P, -1, P) % P for x in points if x != u and x != v]
    assert len(set(ratios)) == len(points) - 2 and 0 not in ratios
    alternatives = Counter(x * y % P for x, y in combinations(ratios, 2))
    # The barycentric ratio when varying x is mu/f(x), so all entries for mu
    # are collected by multiplying each candidate target by f(x).
    charges = Counter()
    for target, multiplicity in alternatives.items():
        cost = penalty(multiplicity)
        if cost:
            for ratio in ratios:
                charges[target * ratio % P] += cost
    return max(charges.values(), default=0)


def main():
    z = pow(G, 8, P)
    points = [pow(z, i, P) for i in range(N)]
    assert pow(z, 64, P) == P - 1 and len(set(points)) == N
    bounds = [fixed_pair(points, points[0], points[d]) for d in range(1, 64)]
    assert bounds == [9 if d % 2 else 12 for d in range(1, 64)]
    for d in (1, 2, 31, 62):
        # Directly check that swapping and translating exponents preserve the result.
        assert fixed_pair(points, points[17], points[(17 - d) % 128]) == bounds[d-1]
    for errors in range(3, 63):
        choices = (comb(errors, 2) - errors // 2) * comb(128-errors, 63-errors)
        assert choices * 186 >= 66 * 6 * 57_660
    upper = comb(128, 61) // 57_660
    assert upper == 361269899996423739323753777598085 < BUDGET
    assert 128 * BUDGET < comb(128, 65)
    print("63 separations. Worst penalty is 9 sixths at odd separations "
          "and 12 sixths at even nonantipodal separations.")
    print(f"List at 62 errors ≤ {upper}; budget {BUDGET}.")
    print("The prescribed-product lower bound exceeds budget at 63 errors.")


if __name__ == "__main__":
    main()
