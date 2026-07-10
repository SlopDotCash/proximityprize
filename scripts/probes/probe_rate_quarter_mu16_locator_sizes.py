#!/usr/bin/env python3
"""Exact census of disjoint collinear locator triples on ``mu_16``.

For three disjoint exponent sets ``A,B,C`` of the same size ``d``, let
``p_A,p_B,p_C`` be their monic locators.  The three corresponding primitive
polynomial lines can share the three pair cores precisely when the vectors of
non-leading coefficients of these locators are affinely collinear.

The original rate-quarter construction uses ``d=3``.  This probe exhausts all
possible sizes ``1 <= d <= 5`` (three disjoint blocks cannot be larger on a
16-point group) and therefore tests whether the same ``mu_16`` lift admits
larger pair cores.  Enumeration is by unordered disjoint triples, avoiding the
much larger scan over all field-valued affine parameters.
"""

from __future__ import annotations

from itertools import combinations
import sys


P = int(sys.argv[1]) if len(sys.argv) > 1 else 97
ORDER = int(sys.argv[2]) if len(sys.argv) > 2 else 16


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
    return out[:-1]


def affine_parameter(
    a: tuple[int, ...], b: tuple[int, ...], c: tuple[int, ...]
) -> int | None:
    """Return lambda with c=a+lambda*(b-a), or ``None`` if absent."""
    pivot = next((j for j, (x, y) in enumerate(zip(a, b)) if x != y), None)
    if pivot is None:
        return None
    lam = (c[pivot] - a[pivot]) * pow((b[pivot] - a[pivot]) % P, P - 2, P) % P
    if all((z - x - lam * (y - x)) % P == 0 for x, y, z in zip(a, b, c)):
        return lam
    return None


def census(mu: tuple[int, ...], d: int) -> dict[str, object]:
    blocks = list(combinations(range(ORDER), d))
    block_index = {block: i for i, block in enumerate(blocks)}
    masks = [sum(1 << e for e in block) for block in blocks]
    coeffs = [locator(mu, block) for block in blocks]
    hits: list[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], int]] = []
    tested = 0
    for ia, a in enumerate(blocks):
        ma = masks[ia]
        for ib in range(ia + 1, len(blocks)):
            mb = masks[ib]
            if ma & mb:
                continue
            remaining = tuple(e for e in range(ORDER) if not ((ma | mb) >> e) & 1)
            for c in combinations(remaining, d):
                ic = block_index[c]
                if ic <= ib:
                    continue
                tested += 1
                lam = affine_parameter(coeffs[ia], coeffs[ib], coeffs[ic])
                if lam is not None:
                    hits.append((a, blocks[ib], blocks[ic], lam))
    return {
        "root_block_size": d,
        "locator_count": len(blocks),
        "unordered_disjoint_triples_tested": tested,
        "collinear_triples": len(hits),
        "first_hits": hits[:10],
    }


def main() -> None:
    assert (P - 1) % ORDER == 0
    omega = pow(primitive_root(), (P - 1) // ORDER, P)
    mu = tuple(pow(omega, e, P) for e in range(ORDER))
    rows = [census(mu, d) for d in range(1, ORDER // 3 + 1)]
    print({"p": P, "mu_order": ORDER, "rows": rows})


if __name__ == "__main__":
    main()
