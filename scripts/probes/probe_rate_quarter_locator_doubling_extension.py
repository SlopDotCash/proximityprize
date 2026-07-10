#!/usr/bin/env python3
"""Search a doubling extension of the universal ``mu_16`` locator triangle.

The seed has three disjoint degree-three locators on ``mu_16`` in one affine
plane relation.  After composition with ``X^2`` it gives degree-six locators
on ``mu_32``.  If one can append one new, mutually disjoint root to each
locator while preserving affine collinearity, the resulting degree is seven,
namely ``32/4-1``.  Iterating such a move would approach the maximal useful
pair-core size for the rate-quarter primitive-line construction.

This script exhausts all ordered choices of the three appended roots and
prints every exact extension over a prime containing ``mu_32``.
"""

from __future__ import annotations

from itertools import permutations
import sys


P = int(sys.argv[1]) if len(sys.argv) > 1 else 193
ORDER = 32


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
    assert out[-1] == 1
    return out


def affine_parameter(
    a: tuple[int, ...], b: tuple[int, ...], c: tuple[int, ...]
) -> int | None:
    # Ignore the equal monic leading coefficient.
    aa, bb, cc = a[:-1], b[:-1], c[:-1]
    pivot = next((j for j, (x, y) in enumerate(zip(aa, bb)) if x != y), None)
    if pivot is None:
        return None
    lam = (cc[pivot] - aa[pivot]) * pow((bb[pivot] - aa[pivot]) % P, P - 2, P) % P
    if all((z - x - lam * (y - x)) % P == 0 for x, y, z in zip(aa, bb, cc)):
        return lam
    return None


def main() -> None:
    assert (P - 1) % ORDER == 0
    omega = pow(primitive_root(), (P - 1) // ORDER, P)
    mu = tuple(pow(omega, e, P) for e in range(ORDER))

    seed16 = ((0, 1, 8), (2, 9, 10), (3, 5, 7))
    lifted = [tuple(sorted(e for a in block for e in (a, a + 16))) for block in seed16]
    assert all(len(block) == 6 for block in lifted)
    assert not (set(lifted[0]) & set(lifted[1]))
    assert not (set(lifted[0]) & set(lifted[2]))
    assert not (set(lifted[1]) & set(lifted[2]))

    used = set().union(*(set(block) for block in lifted))
    remaining = tuple(e for e in range(ORDER) if e not in used)
    hits: list[dict[str, object]] = []
    for ea, eb, ec in permutations(remaining, 3):
        roots = (
            tuple(sorted((*lifted[0], ea))),
            tuple(sorted((*lifted[1], eb))),
            tuple(sorted((*lifted[2], ec))),
        )
        polys = tuple(locator(mu, block) for block in roots)
        lam = affine_parameter(polys[0], polys[1], polys[2])
        if lam is not None:
            hits.append({"roots": roots, "lambda": lam, "locators": polys})

    print({
        "p": P,
        "mu_order": ORDER,
        "lifted_seed": lifted,
        "remaining_exponents": remaining,
        "ordered_extensions_tested": len(remaining) * (len(remaining) - 1) * (len(remaining) - 2),
        "extensions": len(hits),
        "first_hits": hits[:10],
    })


if __name__ == "__main__":
    main()
