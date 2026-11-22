#!/usr/bin/env python3
"""Check the auxiliary six-row bound and the exact interval of 128-bit budgets."""
from collections import Counter
from itertools import combinations
from math import comb, isqrt


def maximum_charge(prime, subgroup, separation):
    v = subgroup[separation]
    ratios = [(x - 1) * pow(x - v, -1, prime) % prime for x in subgroup if x not in (1, v)]
    pairs = Counter(a * b % prime for a, b in combinations(ratios, 2))
    charges = Counter()
    for product, count in pairs.items():
        if count < 2:
            continue
        for value in ratios:
            charges[product * value % prime] += 1 if count == 2 else 3
    return max(charges.values(), default=0)


def main():
    prime = 167772161
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    z = pow(3, (prime - 1) // 128, prime)
    assert pow(z, 64, prime) == prime - 1
    group = [pow(z, i, prime) for i in range(128)]
    bounds = [maximum_charge(prime, group, 2**i) for i in range(6)]
    assert bounds == [9, 12, 12, 12, 12, 12]
    lower = comb(128, 61) // 57660
    upper = (comb(128, 65) - 1) // 128
    assert lower * 2**128 > 2**224 and (upper + 1) <= 2**129
    assert 2**((2 * 3 + 1) * 64) == (2**224)**2
    print(f"Six row maxima {bounds}; exact eligible integer budgets [{lower}, {upper}].")


if __name__ == "__main__":
    main()
