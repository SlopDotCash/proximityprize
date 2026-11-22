#!/usr/bin/env python3
"""Check the genus variance on actual permutation triples and the exact quarter-prefix thresholds."""
from fractions import Fraction
from itertools import combinations
from math import ceil, gcd, lcm


def cycles(permutation):
    remaining = set(range(len(permutation)))
    lengths = []
    while remaining:
        point = next(iter(remaining))
        size = 0
        while point in remaining:
            remaining.remove(point)
            size += 1
            point = permutation[point]
        lengths.append(size)
    return lengths


def inverse(permutation):
    result = list(permutation)
    for i, j in enumerate(permutation):
        result[j] = i
    return result


def verify_triple(m, a, b):
    cycle = list(range(1, m)) + [0]
    swap = list(range(m))
    swap[a], swap[b] = b, a
    last = inverse([cycle[swap[j]] for j in range(m)])
    branch = [cycle, swap, last]
    indices = [m - len(cycles(sigma)) for sigma in branch]
    assert sum(indices) == 2*m-2
    pairs = [(i, j) for i in range(m) for j in range(m) if i != j]
    address = {pair: i for i, pair in enumerate(pairs)}
    pair_indices = []
    excess = -2
    fixed_sum = fixed_squares = 0
    for sigma in branch:
        lengths = cycles(sigma)
        order = lcm(*lengths)
        excess += 1 - Fraction(1, order)
        for j in range(1, order):
            fixed = sum(k for k in lengths if j % k == 0)
            fixed_sum += Fraction(fixed, order)
            fixed_squares += Fraction(fixed**2, order)
        pair_perm = [address[sigma[i], sigma[j]] for i, j in pairs]
        count = len(cycles(pair_perm))
        assert count == sum(gcd(r, s) for r in lengths for s in lengths)-len(lengths)
        pair_indices.append(len(pairs)-count)
    euler = sum(pair_indices)-2*len(pairs)
    assert fixed_sum == m*excess+2
    assert euler == m*m*excess+2-fixed_squares
    assert euler*(excess+2) <= 2*(m-1)**2*excess


def main():
    count = 0
    for m in range(3, 19):
        for a, b in combinations(range(m), 2):
            if gcd(m, b-a) == 1:
                verify_triple(m, a, b)
                count += 1
    print(f"Verified pair genus, variance and pair-cycle formula on {count} symmetric branch triples.")
    n, degree = 2**30, 2**28-2
    genus_floors = []
    for prefix, h, numerator in [
        (19173961, 1, 559999), (38347922, 2, 245613),
        (134217727, 1, 64516), (268435454, 2, 31746),
    ]:
        lower = Fraction(2*(degree**3-8*h*n**2), 4*n**2*(prefix+h)-degree**3)
        assert lower > Fraction(numerator, 10**6)
        if prefix == 19173961:
            assert lower > Fraction(1, 2)
        elif prefix == 38347922:
            assert 1-Fraction(1, 2)-Fraction(1, 4)-Fraction(1, 227) < lower
            assert 1-Fraction(1, 2)-Fraction(1, 4)-Fraction(1, 228) >= lower
        floor = ceil(1+(prefix//h-1)*(Fraction(degree**3, 2*h*n**2)-4)/2)
        genus_floors.append(floor)
        print(f"t={prefix}, h={h}, E >= {lower}, pair genus >= {floor}")
    assert min(genus_floors) == 40210669315222


if __name__ == "__main__":
    main()
