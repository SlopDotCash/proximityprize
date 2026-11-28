#!/usr/bin/env python3
"""Check the named quarter-rate cyclic cross-ratio exponent and valuation bounds."""
from itertools import combinations, product
from math import gcd


def span_and_pairs(a, n):
    gaps = [j-i for i, j in combinations(a, 2)]
    triangles = [gcd(j-i, k-i) for i, j, k in combinations(a, 3)]
    degree_floor = a[3]+a[2]-a[1]-sum(triangles)
    return sum(gcd(n, v) for v in gaps), degree_floor


def dyadic_bounds():
    for level in range(7, 31):
        n = 2**level
        m = n//4
        # On L>=2M, both L/2>4sqrt(L)-1 and L/2>L/3+9.
        assert (2*m+2)**2 > 64*(2*m)
        assert 2*m > 54
        assert m+8 < 2*m
        assert n//2+4 <= 9*n//16
    survivors = []
    for tail in combinations(range(1, 43), 3):
        if gcd(*tail) != 1:
            continue
        a = (0, *tail)
        roots, floor = span_and_pairs(a, 64)
        if roots >= 38 and floor <= 15:
            survivors.append(a)
    assert survivors == [(0, 15, 16, 32), (0, 16, 17, 32)]
    # For N=64, m>=13 and 2r-3m>36 force r>=38.
    assert all(2*r-3*m <= 36 for m in range(16) for r in range(min(37, 3*m)+1))
    assert 43-6 > 2*15 and (43-15)**2 > 16*43
    print("order-64 candidate exponent tuples", survivors)


def local_valuation_control():
    # Congruence orders supply finite ultrametric models for all four-point types.
    def order(x, y):
        n = abs(x-y)
        if not n:
            return 4
        return (n & -n).bit_length()-1

    for values in product(range(8), repeat=4):
        w = {(i, j): order(values[i], values[j]) for i, j in combinations(range(4), 2)}
        pairings = ((w[0, 1]+w[2, 3]), (w[0, 2]+w[1, 3]), (w[0, 3]+w[1, 2]))
        groups = sum(min(w[i, j], w[i, k], w[j, k]) for i, j, k in combinations(range(4), 3))
        assert min(pairings) <= groups
    print("four-point valuation configurations", 8**4)


if __name__ == "__main__":
    dyadic_bounds()
    local_valuation_control()
