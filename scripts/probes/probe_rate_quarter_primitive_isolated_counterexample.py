#!/usr/bin/env python3
"""Construct a rate-quarter half-predecessor counterexample candidate.

The determinant-collapse analysis leaves one honest residual: points on a
collapsed polynomial-line cluster whose fresh agreement lies outside every
cluster core.  This probe realizes that residual explicitly.

For k=7 and n=4k=28, choose three degree-<k polynomial lines

    c_i = f_i * (X, 1)

whose pair differences have three disjoint five-root sets.  Their 14-point
cores cover 27 coordinates.  Every covered coordinate gives one nonjoint bad
scalar gamma=-x, while the single uncovered coordinate gives one scalar on
each of the three lines.  The target is therefore 27+3=30>28 bad scalars.

The script searches only for the split-polynomial seed and for a generic hole;
after that it checks every witness directly, including:

* each core has size 2k;
* pair-core intersections are the prescribed disjoint root sets;
* every q_{i,x}=f_i*(X+gamma) has degree < k;
* q_{i,x} agrees on D_i union {x}, of size 2k+1;
* the received pair is not jointly degree-<k explainable there (the 2k-point
  core uniquely fixes the explaining pair, which fails at x);
* all 30 displayed scalars are distinct after the expected covered-coordinate
  identifications.

This is an executable exact certificate over a prime field, not a Lean proof.
"""

from __future__ import annotations

import random
from dataclasses import dataclass


P = 101
K = 7
N = 4 * K
S = K - 2
SEED = 20260710


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] % P == 0:
        a.pop()
    return [x % P for x in a]


def add(a: list[int], b: list[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out)


def scale(c: int, a: list[int]) -> list[int]:
    return trim([(c * x) % P for x in a])


def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def eval_poly(a: list[int], x: int) -> int:
    out = 0
    for c in reversed(a):
        out = (out * x + c) % P
    return out


def root_poly(roots: set[int]) -> list[int]:
    out = [1]
    for x in sorted(roots):
        out = mul(out, [(-x) % P, 1])
    return out


def roots(a: list[int]) -> set[int]:
    return {x for x in range(P) if eval_poly(a, x) == 0}


def inv(x: int) -> int:
    assert x % P
    return pow(x % P, P - 2, P)


@dataclass(frozen=True)
class Seed:
    e12: frozenset[int]
    e23: frozenset[int]
    e13: frozenset[int]
    f1: tuple[int, ...]
    f2: tuple[int, ...]
    f3: tuple[int, ...]


def find_seed(rng: random.Random) -> Seed:
    nonzero = list(range(1, P))
    for trial in range(1, 2_000_001):
        e12 = set(rng.sample(nonzero, S))
        available = [x for x in nonzero if x not in e12]
        e23 = set(rng.sample(available, S))
        p12 = root_poly(e12)
        c = rng.randrange(1, P - 1)  # excludes -1, so the sum stays degree S
        p23 = scale(c, root_poly(e23))
        p13 = add(p12, p23)
        e13 = roots(p13)
        if len(e13) != S:
            continue
        if 0 in e13 or e13 & e12 or e13 & e23:
            continue
        print(f"split seed found after {trial} trials")
        return Seed(
            frozenset(e12),
            frozenset(e23),
            frozenset(e13),
            (0,),
            tuple(p12),
            tuple(p13),
        )
    raise RuntimeError("no split seed found")


def choose_blocks(seed: Seed, rng: random.Random):
    used_roots = set(seed.e12 | seed.e23 | seed.e13)
    remaining = [x for x in range(1, P) if x not in used_roots]
    fs = [list(seed.f1), list(seed.f2), list(seed.f3)]
    for _ in range(100_000):
        picked = rng.sample(remaining, 13)
        u1, u2, u3 = map(set, (picked[0:4], picked[4:8], picked[8:12]))
        hole = picked[12]
        unique_blocks = [u1, u2, u3]
        core1 = set(seed.e12 | seed.e13) | u1
        core2 = set(seed.e12 | seed.e23) | u2
        core3 = set(seed.e13 | seed.e23) | u3
        cores = [core1, core2, core3]
        union = set().union(*cores)
        assert len(union) == N - 1 and hole not in union

        safe = {(-x) % P for x in union}
        unsafe = []
        ok = True
        for f in fs:
            fx = eval_poly(f, hole)
            if fx == 1:
                ok = False
                break
            gamma = fx * hole * inv(1 - fx) % P
            unsafe.append(gamma)
        if not ok or len(set(unsafe)) != 3 or safe & set(unsafe):
            continue
        return unique_blocks, hole, cores, safe, unsafe
    raise RuntimeError("no generic unique blocks/hole found")


def main() -> None:
    rng = random.Random(SEED)
    seed = find_seed(rng)
    unique_blocks, hole, cores, safe, unsafe = choose_blocks(seed, rng)
    fs = [list(seed.f1), list(seed.f2), list(seed.f3)]

    domain = sorted(set().union(*cores, {hole}))
    assert len(domain) == N
    assert all(len(core) == 2 * K for core in cores)
    assert cores[0] & cores[1] == set(seed.e12)
    assert cores[1] & cores[2] == set(seed.e23)
    assert cores[0] & cores[2] == set(seed.e13)
    assert not (cores[0] & cores[1] & cores[2])

    # Received residual pair.  On a core D_i it equals f_i*(X,1).
    u0: dict[int, int] = {}
    u1: dict[int, int] = {}
    for x in domain:
        owners = [i for i, core in enumerate(cores) if x in core]
        if not owners:
            assert x == hole
            u0[x], u1[x] = 0, 1
            continue
        values = {eval_poly(fs[i], x) for i in owners}
        assert len(values) == 1
        value = values.pop()
        u0[x], u1[x] = value * x % P, value

    witnesses: dict[int, list[tuple[int, int]]] = {}
    for i, (f, core) in enumerate(zip(fs, cores)):
        # The line pair is (a_i,r_i)=(X*f_i,f_i).
        ai = mul(f, [0, 1])
        ri = f
        assert len(ai) - 1 < K and len(ri) - 1 < K
        for x in domain:
            if x in core:
                continue
            denom = (u1[x] - eval_poly(ri, x)) % P
            numer = (eval_poly(ai, x) - u0[x]) % P
            assert denom
            gamma = numer * inv(denom) % P
            q = add(ai, scale(gamma, ri))
            assert len(q) - 1 < K
            support = set(core) | {x}
            assert len(support) == 2 * K + 1
            for y in support:
                lhs = eval_poly(q, y)
                rhs = (u0[y] + gamma * u1[y]) % P
                assert lhs == rhs

            # Core uniqueness: any degree-<K joint explanation on the support
            # must equal (a_i,r_i), which fails as a pair at the fresh point.
            assert any(
                (eval_poly(poly, x) - row[x]) % P
                for poly, row in ((ai, u0), (ri, u1))
            )
            witnesses.setdefault(gamma, []).append((i, x))

    # Covered coordinates produce exactly gamma=-x, independent of source line.
    for x in set().union(*cores):
        gammas = {
            g
            for g, ws in witnesses.items()
            if any(y == x for _, y in ws)
        }
        assert gammas == {(-x) % P}
    # The hole produces one distinct scalar on each of the three lines.
    hole_gammas = {
        g for g, ws in witnesses.items() if any(y == hole for _, y in ws)
    }
    assert hole_gammas == set(unsafe)

    expected = (N - 1) + 3
    assert len(witnesses) == expected == 30
    assert len(witnesses) > N

    print({
        "p": P,
        "n": N,
        "k": K,
        "threshold": 2 * K + 1,
        "bad_scalar_lower_bound": len(witnesses),
        "domain_bound_refuted": len(witnesses) > N,
        "E12": sorted(seed.e12),
        "E23": sorted(seed.e23),
        "E13": sorted(seed.e13),
        "f1": list(seed.f1),
        "f2": list(seed.f2),
        "f3": list(seed.f3),
        "unique_blocks": [sorted(x) for x in unique_blocks],
        "hole": hole,
        "domain": domain,
        "u0": [u0[x] for x in domain],
        "u1": [u1[x] for x in domain],
        "safe_scalars": sorted(safe),
        "unsafe_scalars": sorted(unsafe),
    })


if __name__ == "__main__":
    main()
