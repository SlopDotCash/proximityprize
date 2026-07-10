#!/usr/bin/env python3
"""Cross-prime census of four-line extensions of the universal mu_16 triangle.

For each split prime, keep the fixed universal factors

    0, (1-lambda)L_A, L_C

and enumerate a fourth split cubic `c` for which `c`, `c-a`, and `c-b` are
also scalar multiples of mu_16 locators.  A record consists only of the three
root triples, so intersecting records across several split primes removes
characteristic-specific coincidences while retaining universal identities.
"""

from __future__ import annotations

from itertools import combinations


PRIMES = (97, 193, 257, 353)


def primitive_root(p: int) -> int:
    factors = []
    n = p - 1
    q = 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    return next(g for g in range(2, p)
                if all(pow(g, (p - 1) // q, p) != 1 for q in factors))


def add(a, b, p):
    return tuple((x + y) % p for x, y in zip(a, b))


def sub(a, b, p):
    return tuple((x - y) % p for x, y in zip(a, b))


def scale(s, a, p):
    return tuple(s * x % p for x in a)


def mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return tuple(out)


def locator(mu, roots, p):
    out = (1,)
    for e in roots:
        out = mul(out, ((-mu[e]) % p, 1), p)
    return out


def census(p: int):
    z = pow(primitive_root(p), (p - 1) // 16, p)
    mu = tuple(pow(z, e, p) for e in range(16))
    triples = tuple(combinations(range(16), 3))
    locators = {R: locator(mu, R, p) for R in triples}
    split = {}
    for R, L in locators.items():
        for s in range(1, p):
            split[scale(s, L, p)] = R

    A, B, C = (0, 1, 8), (2, 9, 10), (3, 5, 7)
    pa, pb, pc = locators[A], locators[B], locators[C]
    pivot = next(j for j in range(3) if pa[j] != pb[j])
    lam = (pc[pivot] - pa[pivot]) * pow((pb[pivot] - pa[pivot]) % p, p - 2, p) % p
    a = scale(1 - lam, pa, p)
    b = pc
    assert sub(b, a, p) in split and split[sub(b, a, p)] == B

    records = set()
    for c, Rc in split.items():
        ca = sub(c, a, p)
        cb = sub(c, b, p)
        if ca in split and cb in split and c not in {a, b}:
            records.add((Rc, split[ca], split[cb]))
    return records


def main() -> None:
    censuses = {p: census(p) for p in PRIMES}
    common = set.intersection(*censuses.values())
    print({
        "per_prime_counts": {p: len(v) for p, v in censuses.items()},
        "universal_survivor_count": len(common),
        "universal_survivors": sorted(common),
    })


if __name__ == "__main__":
    main()
