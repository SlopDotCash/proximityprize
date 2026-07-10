#!/usr/bin/env python3
"""Search four cubic polynomial lines with split pair differences on ``mu_16``.

After translating one line to zero, a four-line primitive construction needs
three cubic polynomials ``a,b,c`` such that all six nonzero differences among
``0,a,b,c`` split completely over ``mu_16``.  Such a clique can create
three-owner coordinates as well as pair-owner coordinates and may beat the
known three-line rate-quarter construction.

The first phase asks whether the known universal triangle extends.  The second
phase performs a complete normalized search: scaling lets us require the first
nonzero polynomial to be a monic locator.  Exact collision partitions on the
16 roots are reported for every first hit.
"""

from __future__ import annotations

from itertools import combinations
import sys


P = int(sys.argv[1]) if len(sys.argv) > 1 else 97
ORDER = 16
DEGREE = 3


def primitive_root() -> int:
    factors: list[int] = []
    n = P - 1
    q = 2
    while q * q <= n:
        if n % q == 0:
            factors.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        factors.append(n)
    for g in range(2, P):
        if all(pow(g, (P - 1) // q, P) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((x + y) % P for x, y in zip(a, b))


def sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((x - y) % P for x, y in zip(a, b))


def scale(s: int, a: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(s * x % P for x in a)


def mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return tuple(out)


def locator(mu: tuple[int, ...], roots: tuple[int, ...]) -> tuple[int, ...]:
    out = (1,)
    for e in roots:
        out = mul(out, ((-mu[e]) % P, 1))
    assert len(out) == DEGREE + 1 and out[-1] == 1
    return out


def eval_poly(f: tuple[int, ...], x: int) -> int:
    out = 0
    for coefficient in reversed(f):
        out = (out * x + coefficient) % P
    return out


def collision_classes(fs: tuple[tuple[int, ...], ...], mu: tuple[int, ...]):
    rows = []
    for e, x in enumerate(mu):
        buckets: dict[int, list[int]] = {}
        for i, f in enumerate(fs):
            buckets.setdefault(eval_poly(f, x), []).append(i)
        rows.append((e, tuple(sorted(tuple(v) for v in buckets.values()))))
    return rows


def main() -> None:
    assert (P - 1) % ORDER == 0
    omega = pow(primitive_root(), (P - 1) // ORDER, P)
    mu = tuple(pow(omega, e, P) for e in range(ORDER))

    roots_of: dict[tuple[int, ...], tuple[int, ...]] = {}
    monic: list[tuple[int, ...]] = []
    for roots in combinations(range(ORDER), DEGREE):
        p = locator(mu, roots)
        monic.append(p)
        for s in range(1, P):
            roots_of[scale(s, p)] = roots
    split = set(roots_of)
    zero = (0,) * (DEGREE + 1)

    # Known triangle in the orientation f1=0, f2=(1-lambda)p_A, f3=p_C.
    a_roots, b_roots, c_roots = ((0, 1, 8), (2, 9, 10), (3, 5, 7))
    pa, pb, pc = (locator(mu, roots) for roots in (a_roots, b_roots, c_roots))
    pivot = next(j for j in range(DEGREE) if pa[j] != pb[j])
    lam = (pc[pivot] - pa[pivot]) * pow((pb[pivot] - pa[pivot]) % P, P - 2, P) % P
    assert pc == add(scale(1 - lam, pa), scale(lam, pb))
    known_a = scale(1 - lam, pa)
    known_b = pc
    assert known_a in split and known_b in split and sub(known_b, known_a) in split
    known_extensions = [
        c for c in split
        if sub(c, known_a) in split and sub(c, known_b) in split
        and c not in {known_a, known_b}
    ]

    # Complete search modulo a common nonzero scalar.  The first vertex from
    # zero can therefore be chosen from the monic locator table.
    first_hits = []
    triangles_tested = 0
    for a in monic:
        neighbors_a = {
            b for b in split if b != a and sub(b, a) in split
        }
        for b in neighbors_a:
            triangles_tested += 1
            for c in neighbors_a:
                if c in {a, b}:
                    continue
                if sub(c, b) not in split:
                    continue
                fs = (zero, a, b, c)
                first_hits.append({
                    "polynomials": fs,
                    "pair_root_sets": {
                        "01": roots_of[a],
                        "02": roots_of[b],
                        "03": roots_of[c],
                        "12": roots_of[sub(b, a)],
                        "13": roots_of[sub(c, a)],
                        "23": roots_of[sub(c, b)],
                    },
                    "collision_classes": collision_classes(fs, mu),
                })
                if len(first_hits) >= 10:
                    break
            if len(first_hits) >= 10:
                break
        if len(first_hits) >= 10:
            break

    print({
        "p": P,
        "mu_order": ORDER,
        "split_cubic_directions": len(split),
        "known_triangle_extensions": len(known_extensions),
        "known_first_extensions": known_extensions[:10],
        "normalized_triangles_tested_before_stop": triangles_tested,
        "four_cliques_found_before_stop": len(first_hits),
        "first_hits": first_hits,
    })


if __name__ == "__main__":
    main()
