#!/usr/bin/env python3
"""Check that the two-error heavy charge comparisons on mu_128 lift for p>=2^115."""

from bisect import bisect_left
from collections import defaultdict
from functools import cache
from itertools import combinations
from math import gcd, isqrt, prod

ORDER = 128
DEGREE = ORDER // 2
AUXILIARY_PRIME = 167_772_161
AUXILIARY_ROOT = 370_529
SCALE = 1 << 28
MINIMUM_PRIME_BITS = 115


@cache
def twice_cosine(order, exponent):
    """Outward bounds for SCALE*2*cos(2*pi*exponent/order)."""
    if order == 2:
        value = 2 * SCALE * (-1 if exponent % 2 else 1)
        return value, value
    if 4 * exponent in (order, 3 * order):
        return 0, 0
    lower, upper = twice_cosine(order // 2, exponent % (order // 2))
    lower = isqrt(max(0, (2 * SCALE + lower) * SCALE))
    upper = isqrt((2 * SCALE + upper) * SCALE) + 1
    if order < 4 * exponent < 3 * order:
        return -upper, -lower
    return lower, upper


@cache
def chord_squared(exponent):
    """Upper bound for SCALE*abs(zeta^exponent-1)^2."""
    return 2 * SCALE - twice_cosine(ORDER, exponent % ORDER)[0]


def height_bound(separation, sites):
    """Bound the product of Euclidean norms of the normalized coordinate vectors."""
    num_v = sum(gcd(x, ORDER) for x in sites)
    den_v = sum(gcd(x - separation, ORDER) for x in sites)
    common_v = min(num_v, den_v)
    factors = []
    for j in range(1, DEGREE, 2):
        a = prod(chord_squared(j * x % ORDER) for x in sites)
        b = prod(chord_squared(j * (x - separation) % ORDER) for x in sites)
        factors.append(a + b)
    denominator = (SCALE ** (len(factors) * len(sites))) << common_v
    return (prod(factors) + denominator - 1) // denominator


def cyclotomic_product(left, right):
    """Multiply modulo X^degree+1 with integer coefficients."""
    degree = len(left)
    coefficients = [0] * (2 * degree)
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                if b:
                    coefficients[i + j] += a * b
    return [a - b for a, b in zip(coefficients, coefficients[degree:])]


def binomial_product(factors):
    """Compute a product of (X^site-X^root) modulo X^64+1."""
    coefficients = [1] + [0] * (DEGREE - 1)
    for root, site in factors:
        result = [0] * DEGREE
        for i, value in enumerate(coefficients):
            for j, sign in ((site, 1), (root, -1)):
                exponent = (i + j) % ORDER
                result[exponent % DEGREE] += value * sign * (1 if exponent < DEGREE else -1)
        coefficients = result
    return coefficients


def comparison(separation, left, right):
    """Clear the two ratio products in Z[zeta]."""
    a = binomial_product([(0, x) for x in left] + [(separation, y) for y in right])
    b = binomial_product([(separation, x) for x in left] + [(0, y) for y in right])
    return [x - y for x, y in zip(a, b)]


def absolute_norm(coefficients):
    """At each quadratic step take (A+XB)(A-XB)=A^2-X^2*B^2."""
    while len(coefficients) > 1:
        even, odd = coefficients[::2], coefficients[1::2]
        a = cyclotomic_product(even, even)
        b = cyclotomic_product(odd, odd)
        coefficients = [a[0] + b[-1]] + [x - y for x, y in zip(a[1:], b)]
    return abs(coefficients[0])


def check_row(separation, prime_bits):
    sites = [x for x in range(1, ORDER) if x != separation]
    p = AUXILIARY_PRIME
    roots = [pow(AUXILIARY_ROOT, x, p) for x in range(ORDER)]
    assert roots[DEGREE] == p - 1 and len(set(roots)) == ORDER
    ratios = {x: (roots[x] - 1) * pow(roots[x] - roots[separation], -1, p) % p for x in sites}
    fibers = defaultdict(list)
    for a, b in combinations(sites, 2):
        fibers[ratios[a] * ratios[b] % p].append((a, b))

    records = []
    for pairs in fibers.values():
        if len(pairs) < 2:
            continue
        rep = pairs[0]
        for pair in pairs[1:]:
            assert not any(comparison(separation, rep, pair))
        records.extend((*rep, x) for x in sites)

    heights = sorted((height_bound(separation, triple), triple) for triple in records)
    bounds = [height for height, _ in heights]
    limit = 1 << (2 * prime_bits)
    exceptional_count = 0
    max_odd = 0
    for i, (height, left) in enumerate(heights):
        start = bisect_left(bounds, (limit + height - 1) // height, i + 1)
        for _, right in heights[start:]:
            norm = absolute_norm(comparison(separation, left, right))
            if norm:
                odd_part = norm // (norm & -norm)
                assert odd_part < limit, (separation, left, right, odd_part)
                max_odd = max(max_odd, odd_part)
            exceptional_count += 1
    return len(records), exceptional_count, max_odd.bit_length()


if __name__ == "__main__":
    expected = {
        1: (23_058, 1411, 195),
        2: (22_302, 735, 193),
        4: (22_302, 111, 189),
        8: (22_302, 5, 188),
        16: (22_302, 0, 0),
        32: (22_806, 0, 0),
    }
    for d, reference in expected.items():
        result = check_row(d, MINIMUM_PRIME_BITS)
        assert result == reference
        print(f"d={d:2}: records={result[0]}, exact comparisons={result[1]}, "
              f"largest exceptional odd norm uses {result[2]} bits", flush=True)
