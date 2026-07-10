#!/usr/bin/env python3
"""Search root-of-unity locator configurations for the rate-quarter counterexample.

The arbitrary-domain isolated-population construction needs three disjoint root
sets E12,E23,E13 whose monic locators are affinely collinear.  A scale-compatible
construction on a 2-power subgroup would follow by lifting a small configuration
through X |-> X^m.  The first natural cell is therefore three disjoint triples in
mu_16.  This script exhausts that cell exactly over F_97.

For monic locators P,Q,R, affine collinearity is equivalent to their non-leading
coefficient vectors being collinear.  We enumerate every pair and every affine
parameter and look the resulting vector up in the complete locator table.
"""

from __future__ import annotations

from itertools import combinations
import sys


P = int(sys.argv[1]) if len(sys.argv) > 1 else 97
N = 16
R = 3


def primitive_root() -> int:
    factors = []
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


def mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return tuple(out)


def locator(values: tuple[int, ...]) -> tuple[int, ...]:
    out = (1,)
    for x in values:
        out = mul(out, ((-x) % P, 1))
    assert out[-1] == 1
    return out


def main() -> None:
    omega = pow(primitive_root(), (P - 1) // N, P)
    mu = tuple(pow(omega, i, P) for i in range(N))
    entries = []
    lookup: dict[tuple[int, ...], list[frozenset[int]]] = {}
    for inds in combinations(range(N), R):
        roots = frozenset(inds)
        coeff = locator(tuple(mu[i] for i in inds))[:-1]
        entries.append((roots, coeff))
        lookup.setdefault(coeff, []).append(roots)

    hits = set()
    tested = 0
    for a, va in entries:
        for b, vb in entries:
            if min(a) >= min(b) or a & b:
                continue
            direction = tuple((y - x) % P for x, y in zip(va, vb))
            for lam in range(2, P):
                tested += 1
                vc = tuple((x + lam * d) % P for x, d in zip(va, direction))
                for c in lookup.get(vc, ()):
                    if c & a or c & b:
                        continue
                    hit = tuple(sorted((tuple(sorted(a)), tuple(sorted(b)), tuple(sorted(c)))))
                    hits.add(hit)

    special_sets = ((0, 1, 8), (2, 9, 10), (3, 5, 7))
    special_vectors = [locator(tuple(mu[i] for i in inds))[:-1]
                       for inds in special_sets]
    va, vb, vc = special_vectors
    special_lambda = None
    for j, (a, b) in enumerate(zip(va, vb)):
        if a != b:
            special_lambda = (vc[j] - a) * pow((b - a) % P, P - 2, P) % P
            break
    assert special_lambda is not None
    assert all((a + special_lambda * (b - a) - c) % P == 0
               for a, b, c in zip(va, vb, vc))

    print({
        "p": P,
        "mu_order": N,
        "root_block_size": R,
        "locator_count": len(entries),
        "affine_parameters_tested": tested,
        "disjoint_collinear_triples": len(hits),
        "first_hits": sorted(hits)[:10],
        "special_hit": special_sets,
        "special_lambda": special_lambda,
        "special_locator_vectors": special_vectors,
        "mu": mu,
    })


if __name__ == "__main__":
    main()
