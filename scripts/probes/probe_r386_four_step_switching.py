#!/usr/bin/env python3
"""Exact fourfold subgroup representation maxima for the block-switching route."""

from collections import Counter


def factors(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p):
    fs = factors(p - 1)
    return next(g for g in range(2, p)
                if all(pow(g, (p - 1) // q, p) != 1 for q in fs))


def run(n, p):
    assert (p - 1) % n == 0
    zeta = pow(primitive_root(p), (p - 1) // n, p)
    group = [pow(zeta, i, p) for i in range(n)]
    pair = Counter((x + y) % p for x in group for y in group)
    four = Counter()
    items = list(pair.items())
    for a, ca in items:
        for b, cb in items:
            four[(a + b) % p] += ca * cb
    nonzero = [(v, c) for c, v in four.items() if c]
    max_value, argmax = max(nonzero)
    histogram = Counter(four.values())
    print({
        "n": n,
        "p": p,
        "n4_over_p": n ** 4 / p,
        "pair_support": len(pair),
        "four_support": len(four),
        "rep4_zero": four[0],
        "rep4_nonzero_max": max_value,
        "rep4_nonzero_argmax": argmax,
        "max_over_n": max_value / n,
        "top_fiber_sizes": sorted(histogram.items(), reverse=True)[:8],
    })


if __name__ == "__main__":
    for cell in ((8, 40961), (16, 65537), (16, 65617), (32, 1048609)):
        run(*cell)
