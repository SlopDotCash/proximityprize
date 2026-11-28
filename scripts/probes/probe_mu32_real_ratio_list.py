#!/usr/bin/env python3
"""Bound real locator norms and exhibit four half-rate words over a quadratic field."""
from itertools import combinations
from math import prod

from probe_mu32_odd_ratio_norm import N, SCALE, ceil_div, chord


def ratio_bounds(shift, degrees):
    """Expand the eight real-embedding factors and bound each positive term."""
    sites = [a for a in range(1, N) if a != shift]
    totals = dict.fromkeys(degrees, 0)
    for mask in range(256):
        lows, highs = [], []
        for site in sites:
            low = high = SCALE
            for j in range(8):
                if mask & (1 << j):
                    t = 2*j + 1
                    left = chord(t*site % N)
                    right = chord(t*(site-shift) % N)
                    low = low*left[0] // right[1]
                    high = ceil_div(high*left[1], right[0])
            assert low > 0
            lows.append(low)
            highs.append(high)
        lows.sort()
        highs.sort(reverse=True)
        for d in degrees:
            totals[d] += ceil_div(prod(highs[:d]), prod(lows[:d]))
    return totals


P = 32075779469025367711
ONE = (1, 0)
ZERO = (0, 0)


def mul(x, y):
    a, b = x
    c, d = y
    return ((a*c-b*d) % P, (a*d+b*c) % P)


def power(x, n):
    result = ONE
    while n:
        if n % 2:
            result = mul(result, x)
        x = mul(x, x)
        n //= 2
    return result


def vanisher(x, roots):
    result = ONE
    for r in roots:
        result = mul(result, ((x[0]-r[0]) % P, (x[1]-r[1]) % P))
    return result


def quadratic_witness():
    # The full factorization and order checks certify primality by Lucas's test.
    factors = {2: 1, 3: 33, 5: 1, 577: 1}
    assert all(577 % a for a in range(2, 25))
    assert prod(q**e for q, e in factors.items()) == P-1
    assert pow(3, P-1, P) == 1
    assert all(pow(3, (P-1)//q, P) != 1 for q in factors)
    assert P % 32 == 31 and P*P // 2**128 == 3
    # i^2 = -1 gives a field because P is 3 modulo 4.
    exponent = (P*P - 1) // 32
    for a in range(1, 32):
        g = power((a, 1), exponent)
        if power(g, 16) != ONE:
            break
    assert power(g, 32) == ONE and power(g, 16) != ONE and g[1] != 0
    sites = [power(g, j) for j in range(32)]
    # Reserve seven roots in the X^8=1 fiber; any two other fibers give 16 more.
    reserve = sites[::4][:7]
    labels = sites[8::8]
    words_nine = []
    center_nine = [mul(vanisher(x, reserve), power(x, 16)) for x in sites]
    for pair in combinations(labels, 2):
        word = []
        for x, y in zip(sites, center_nine, strict=True):
            gap = mul(vanisher(x, reserve), vanisher(power(x, 8), pair))
            word.append(((y[0] - gap[0]) % P, (y[1] - gap[1]) % P))
        words_nine.append(tuple(word))
    assert len(set(words_nine)) == 3
    assert all(sum(a == b for a, b in zip(w, center_nine, strict=True)) == 23
               for w in words_nine)
    fibers = sites[::4]
    triples = ((3, 6, 7), (3, 5, 7), (4, 5, 6))
    roots = [[fibers[j] for j in indices] for indices in triples]
    scales = [vanisher(fibers[2], r) for r in roots]
    assert all(scale != ZERO for scale in scales)
    inverses = [power(scale, P*P - 2) for scale in scales]
    rows = []
    for x in sites:
        weight = vanisher(x, [sites[j] for j in (0, 1, 4)])
        rows.append([ZERO] + [mul(weight, mul(vanisher(power(x, 4), r), inv))
                              for r, inv in zip(roots, inverses, strict=True)])
    choose = (2, 1, 1, 0, 0, 0, 0, 0)
    center = [row[choose[j % 8]] for j, row in enumerate(rows)]
    words = list(zip(*rows, strict=True))
    assert all(a != b for a, b in combinations(words, 2))
    agreements = [sum(a == b for a, b in zip(word, center, strict=True)) for word in words]
    assert agreements == [22, 22, 22, 24]
    print(f"p={P}, budget=3, primitive root={g}, 9 errors: [23, 23, 23], 10 errors: {agreements}")


if __name__ == "__main__":
    degrees = (7, 8, 9)
    limits = (55, 58, 62)
    results = [ratio_bounds(s, degrees) for s in (1, 2, 4, 8)]
    for d, bits in zip(degrees, limits, strict=True):
        values = [row[d] for row in results]
        assert max(values) < 2**bits
        print(f"degree {d}: {values} < 2^{bits}")
    quadratic_witness()
