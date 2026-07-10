#!/usr/bin/env python3
"""Exact census of primitive-generator roots of signed-walk endpoint polynomials."""

from collections import defaultdict
from math import gcd


def primitive_root(p):
    factors = []
    x = p - 1
    q = 2
    while q * q <= x:
        if x % q == 0:
            factors.append(q)
            while x % q == 0:
                x //= q
        q += 1
    if x > 1:
        factors.append(x)
    return next(a for a in range(2, p)
                if all(pow(a, (p - 1) // q, p) != 1 for q in factors))


def endpoint_histogram(n, length):
    m = n // 2
    hist = {(0,) * m: 1}
    steps = []
    for j in range(m):
        plus = [0] * m
        minus = [0] * m
        plus[j] = 1
        minus[j] = -1
        steps.extend((tuple(plus), tuple(minus)))
    for _ in range(length):
        nxt = defaultdict(int)
        for d, mass in hist.items():
            for step in steps:
                nxt[tuple(x + y for x, y in zip(d, step))] += mass
        hist = nxt
    return hist


def run_cell(n, p, r):
    assert (p - 1) % n == 0
    root = pow(primitive_root(p), (p - 1) // n, p)
    generators = [pow(root, a, p) for a in range(n) if gcd(a, n) == 1]
    hist = endpoint_histogram(n, 2 * r)
    by_roots = defaultdict(lambda: [0, 0])
    examples = {}
    for d, mass in hist.items():
        if not any(d):
            continue
        roots = sum(sum(c * pow(g, j, p) for j, c in enumerate(d)) % p == 0
                    for g in generators)
        by_roots[roots][0] += 1
        by_roots[roots][1] += mass
        examples.setdefault(roots, d)
    max_roots = max(by_roots, default=0)
    print({
        "n": n,
        "p": p,
        "r": r,
        "endpoints": len(hist),
        "generator_count": len(generators),
        "max_roots": max_roots,
        "max_example": examples.get(max_roots),
        "root_histogram": dict(sorted(by_roots.items())),
    })


if __name__ == "__main__":
    for cell in ((8, 17, 2), (8, 41, 2), (8, 73, 3),
                 (16, 97, 2), (16, 113, 2), (16, 193, 3)):
        run_cell(*cell)
