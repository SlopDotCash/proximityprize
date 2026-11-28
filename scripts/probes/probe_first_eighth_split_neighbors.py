#!/usr/bin/env python3
"""Check the saturated-neighbor and three-fiber counts at the first eighth-rate test."""
from fractions import Fraction
from itertools import combinations, product
from math import ceil, comb, floor, prod


def parameters(n, m, t, d):
    quotient, remainder = divmod(m * t, n)
    deficit = m * (m - 1) * d - n * quotient * (quotient - 1) - 2 * quotient * remainder
    edges = m * (m - 1) // 2 - deficit // 2
    common = ceil(Fraction(4 * edges, m) - m)
    gap = t - d
    assert gap > 0 and n * d >= t * t
    spectral = 1 + Fraction(m * (n * d - t * t), n * gap)
    mean = Fraction(d * (n - t), n)
    fluctuation = 2 * gap * spectral * d * (1 - Fraction(d, n))
    return edges, common, mean, fluctuation


def production():
    n, t, d = 2**30, 379_625_061, 2**27 - 1
    edges, common, mean, fluctuation = parameters(n, n + 1, t, d)
    assert (edges, common) == (410_960_812_476_257_241, 457_206_502)
    for width in (20_000, 100_000, 1_000_000):
        low, high = ceil(mean - width), floor(mean + width)
        kept = common - floor(fluctuation / width**2)
        multiplicity = (d // low) * ((t - d) // low)**2
        assert multiplicity == 4
        distinct = ceil(Fraction(kept, multiplicity))
        single_degree = ceil(Fraction(distinct, high - low + 1))
        print(f'degree {low:,} through {high:,}, {kept:,} maps, '
              f'{distinct:,} up to target reparametrization, {single_degree:,} at one degree')
        if width == 100_000:
            assert (low, high, kept, distinct) == (86_664_595, 86_864_594, 449_965_880, 112_491_470)
            half_degree = ceil(Fraction(low, 2))
            assert high // 2 < low
            cap = comb(d // half_degree, 2) * comb((t - d) // half_degree, 2) * ((t - d) // low)
            assert cap == 60 and ceil(Fraction(kept, cap)) == 7_499_432
        if width == 20_000:
            assert single_degree >= 1_727

    density = Fraction(2 * edges, (n + 1)**2)
    affine_ratio = Fraction(n - d, t - d)
    for size, expected, independent in ((13, 13_131_286, 14), (16, 3_616_017, 13), (17, 704_446, 12)):
        common_neighborhood = ceil((n + 1) * density * prod(
            max(0, density - Fraction(floor(affine_ratio**j), n + 1)) for j in range(size - 1)))
        assert common_neighborhood == expected and expected > affine_ratio**(independent - 2)


def small_control():
    # All 2-subsets of four sites realize d=1; parity-balanced variants test pruning too.
    supports = [set(pair) for pair in combinations(range(4), 2)]
    for keep in range(3, 7):
        for family in combinations(supports, keep):
            edges, common, mean, fluctuation = parameters(4, keep, 2, 1)
            anchors = [(a, b) for a, b in combinations(family, 2) if len(a & b) == 1]
            assert len(anchors) >= edges
            assert max(sum(c != a and c != b and len(a & c) == len(b & c) == 1
                           for c in family) for a, b in anchors) >= common
            for a, b in anchors:
                roots = a & b
                assert sum((1 - len(roots & c) - mean)**2 for c in family) <= fluctuation
    # Check explicit split maps on F_17 and every affine change of target preserving
    # the three prescribed coordinate pools, including poles in the anchor intersection.
    p = 17
    sites = range(p)
    base = {x: x**2 % p for x in sites}
    zero_pool = {x for x in sites if base[x] in (1, 4)}
    one_pool = {x for x in sites if base[x] in (9, 16)}
    # Use 1/(X^2-2), whose split fibers are read by their original x^2 labels.
    def evaluate(x):
        return None if base[x] == 2 else pow(base[x] - 2, -1, p)
    # Two is a square in F_17. An allowed target pole must be exactly this entire fiber.
    pole_pool = {x for x in sites if base[x] == 2}
    fibers = {a: {x for x in sites if evaluate(x) == a} for a in [None, *sites]}
    pools = (pole_pool, zero_pool, one_pool)
    choices = [[a for a, roots in fibers.items() if len(roots) == 2 and roots <= pool]
               for pool in pools]
    assert len(list(product(*choices))) == 4
    assert all(len(pool) // 2 == len(targets) for pool, targets in zip(pools, choices))


if __name__ == '__main__':
    production()
    small_control()
