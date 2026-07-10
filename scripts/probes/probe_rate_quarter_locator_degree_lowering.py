#!/usr/bin/env python3
"""Try linear degree-lowering operators on boundary locator triangles.

Degree-``n/4`` locator identities are easy (subgroup-coset binomials and
several nontrivial variants), but the primitive direction needs degree at most
``n/4-1``.  A *common linear* degree-lowering operator preserves every
three-term polynomial relation.  This probe exhausts the degree-four
``mu_16`` triangles, lifts them through ``X -> X^2`` to degree eight on
``mu_32``, and tests two natural operators:

* divided difference ``(F(X)-F(a))/(X-a)``;
* polar derivative ``8F(X)-(X-a)F'(X)``.

For every ``a in mu_32`` it asks whether all three degree-seven images split
into seven distinct, pairwise-disjoint ``mu_32`` roots.  Hits are retested in
both F_193 and F_97; a cross-prime hit is evidence for a cyclotomic identity
rather than a small-characteristic accident.
"""

from __future__ import annotations

from itertools import combinations


def primitive_root(p: int) -> int:
    factors: list[int] = []
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
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def add(a: tuple[int, ...], b: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] = (out[i] + x) % p
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % p
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def scale(s: int, a: tuple[int, ...], p: int) -> tuple[int, ...]:
    return tuple(s * x % p for x in a)


def mul(a: tuple[int, ...], b: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return tuple(out)


def locator(mu: tuple[int, ...], roots: tuple[int, ...], p: int) -> tuple[int, ...]:
    out = (1,)
    for e in roots:
        out = mul(out, ((-mu[e]) % p, 1), p)
    return out


def eval_poly(f: tuple[int, ...], x: int, p: int) -> int:
    out = 0
    for c in reversed(f):
        out = (out * x + c) % p
    return out


def affine_parameter(a, b, c, p: int) -> int | None:
    aa, bb, cc = a[:-1], b[:-1], c[:-1]
    pivot = next((j for j, (x, y) in enumerate(zip(aa, bb)) if x != y), None)
    if pivot is None:
        return None
    lam = (cc[pivot] - aa[pivot]) * pow((bb[pivot] - aa[pivot]) % p, p - 2, p) % p
    if all((z - x - lam * (y - x)) % p == 0 for x, y, z in zip(aa, bb, cc)):
        return lam
    return None


def boundary_hits(p: int):
    omega = pow(primitive_root(p), (p - 1) // 16, p)
    mu = tuple(pow(omega, e, p) for e in range(16))
    blocks = list(combinations(range(16), 4))
    index = {b: i for i, b in enumerate(blocks)}
    masks = [sum(1 << e for e in b) for b in blocks]
    polys = [locator(mu, b, p) for b in blocks]
    hits = []
    for ia, a in enumerate(blocks):
        ma = masks[ia]
        for ib in range(ia + 1, len(blocks)):
            mb = masks[ib]
            if ma & mb:
                continue
            remaining = tuple(e for e in range(16) if not ((ma | mb) >> e) & 1)
            for c in combinations(remaining, 4):
                ic = index[c]
                if ic <= ib:
                    continue
                lam = affine_parameter(polys[ia], polys[ib], polys[ic], p)
                if lam is not None:
                    hits.append((a, blocks[ib], c))
    return hits


def divided_difference(f: tuple[int, ...], a: int, p: int) -> tuple[int, ...]:
    # Synthetic division of F(X)-F(a) by X-a.
    g = list(f)
    g[0] = (g[0] - eval_poly(f, a, p)) % p
    q = [0] * (len(f) - 1)
    q[-1] = g[-1]
    for j in range(len(q) - 2, -1, -1):
        q[j] = (g[j + 1] + a * q[j + 1]) % p
    assert g[0] == (-a * q[0]) % p
    return tuple(q)


def polar_derivative(f: tuple[int, ...], a: int, p: int) -> tuple[int, ...]:
    d = len(f) - 1
    deriv = tuple((j * f[j]) % p for j in range(1, len(f)))
    x_minus_a_deriv = mul(((-a) % p, 1), deriv, p)
    out = add(scale(d, f, p), scale(-1, x_minus_a_deriv, p), p)
    assert len(out) <= d
    return out + (0,) * (d - len(out))


def split_root_exponents(f, mu, p: int):
    roots = tuple(e for e, x in enumerate(mu) if eval_poly(f, x, p) == 0)
    return roots if len(roots) == 7 and len(f) <= 8 else None


def test_triple(blocks, p: int):
    omega = pow(primitive_root(p), (p - 1) // 32, p)
    mu = tuple(pow(omega, e, p) for e in range(32))
    lifted = [tuple(sorted(e for b in block for e in (b, b + 16))) for block in blocks]
    fs = [locator(mu, roots, p) for roots in lifted]
    out = []
    for ea, a in enumerate(mu):
        for name, op in (("divdiff", divided_difference), ("polar", polar_derivative)):
            roots = [split_root_exponents(op(f, a, p), mu, p) for f in fs]
            if any(r is None for r in roots):
                continue
            root_sets = [set(r) for r in roots]
            if any(root_sets[i] & root_sets[j] for i in range(3) for j in range(i)):
                continue
            out.append((name, ea, tuple(roots)))
    return out


def line_direction(blocks, p: int):
    omega = pow(primitive_root(p), (p - 1) // 16, p)
    mu = tuple(pow(omega, e, p) for e in range(16))
    a, b = (locator(mu, block, p) for block in blocks[:2])
    direction = tuple((y - x) % p for x, y in zip(a[:-1], b[:-1]))
    pivot = next(j for j, x in enumerate(direction) if x)
    inv = pow(direction[pivot], p - 2, p)
    return tuple(x * inv % p for x in direction)


def main() -> None:
    hits193 = boundary_hits(193)
    cross_boundary = [blocks for blocks in hits193
                      if affine_parameter(
                          *(locator(tuple(pow(pow(primitive_root(97), 6, 97), e, 97)
                                     for e in range(16)), block, 97)
                            for block in blocks), 97) is not None]
    directions193 = {line_direction(blocks, 193) for blocks in hits193}
    successes = []
    for blocks in hits193:
        for candidate in test_triple(blocks, 193):
            cross = candidate in test_triple(blocks, 97)
            successes.append((blocks, candidate, cross))
    print({
        "boundary_triangles_F193": len(hits193),
        "boundary_directions_F193": len(directions193),
        "cross_prime_boundary_triangles": len(cross_boundary),
        "degree_lowering_successes_F193": len(successes),
        "cross_prime_successes": sum(cross for _, _, cross in successes),
        "first_successes": successes[:20],
    })


if __name__ == "__main__":
    main()
