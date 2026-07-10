#!/usr/bin/env python3
"""Search the n=16, k=4 half-predecessor for a multiple-joint-core counterexample.

At the predecessor agreement threshold t = n/2 + 1 = 9, an 8-set C on which
both stack rows are degree-<4 evaluations is a *joint core*.  Every i outside C
with nonzero direction defect produces one genuine non-joint 9-agreement:

    gamma(C,i) = -(u0_i - I_C(u0)(alpha_i))
                  / (u1_i - I_C(u1)(alpha_i)).

Thus two complementary cores give the known n-scalar packing.  This probe asks
whether a third or fourth compatible core can make more than n distinct ratios.

The search is exact over F_97 on mu_16.  For a core family F, W(F) is the linear
space of words that restrict to a degree-<4 polynomial on every C in F.  We
enumerate a third core over an anchored complementary pair, retain precisely the
families with dim(W/RS) >= 2, and optimize the two stack rows inside W.  We then
greedily enumerate a fourth core from the best triples.  Every reported scalar is
verified directly on its core-plus-one support, including the non-joint defect.

This is a falsifier, not a proof: a maximum <= 16 only rules out the searched
multiple-core architecture over this field/domain and anchor orbit.
"""

from __future__ import annotations

import itertools
import random
from dataclasses import dataclass


P = 97
N = 16
K = 4
T = 9


def inv(x: int) -> int:
    return pow(x % P, P - 2, P)


def primitive_root() -> int:
    factors = (2, 3)
    for g in range(2, P):
        if all(pow(g, (P - 1) // q, P) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


OMEGA = pow(primitive_root(), (P - 1) // N, P)
XS = [pow(OMEGA, i, P) for i in range(N)]


def dot(a: list[int], b: list[int]) -> int:
    return sum(x * y for x, y in zip(a, b)) % P


def rref(matrix: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    a = [[x % P for x in row] for row in matrix]
    if not a:
        return a, []
    ncol = len(a[0])
    pivots: list[int] = []
    r = 0
    for c in range(ncol):
        pivot = next((s for s in range(r, len(a)) if a[s][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = inv(a[r][c])
        a[r] = [(scale * x) % P for x in a[r]]
        for s in range(len(a)):
            if s == r or a[s][c] == 0:
                continue
            scale = a[s][c]
            a[s] = [(x - scale * y) % P for x, y in zip(a[s], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    return a, pivots


def nullspace(matrix: list[list[int]], ncol: int) -> list[list[int]]:
    if not matrix:
        return [[1 if i == j else 0 for i in range(ncol)] for j in range(ncol)]
    rr, pivots = rref(matrix)
    free = [c for c in range(ncol) if c not in pivots]
    out: list[list[int]] = []
    for f in free:
        v = [0] * ncol
        v[f] = 1
        for row, pc in enumerate(pivots):
            v[pc] = (-rr[row][f]) % P
        out.append(v)
    return out


def lagrange_weights(base: tuple[int, ...], x: int) -> list[int]:
    out = []
    for a in base:
        num = 1
        den = 1
        for b in base:
            if a != b:
                num = num * (x - XS[b]) % P
                den = den * (XS[a] - XS[b]) % P
        out.append(num * inv(den) % P)
    return out


def defect_row(core: tuple[int, ...], i: int) -> list[int]:
    """Linear functional u_i - I_core(u)(alpha_i), using four core anchors."""
    base = core[:K]
    row = [0] * N
    row[i] = 1
    for b, w in zip(base, lagrange_weights(base, XS[i])):
        row[b] = (row[b] - w) % P
    return row


def core_constraints(core: tuple[int, ...]) -> list[list[int]]:
    return [defect_row(core, i) for i in core[K:]]


ALL_CORES = list(itertools.combinations(range(N), N // 2))
CONSTRAINTS = {core: core_constraints(core) for core in ALL_CORES}
DEFECTS = {
    core: {i: defect_row(core, i) for i in range(N) if i not in core}
    for core in ALL_CORES
}


def word_from_coeffs(basis: list[list[int]], coeffs: list[int]) -> list[int]:
    return [sum(a * basis[j][i] for j, a in enumerate(coeffs)) % P for i in range(N)]


def core_family_basis(cores: tuple[tuple[int, ...], ...]) -> list[list[int]]:
    equations = [row for core in cores for row in CONSTRAINTS[core]]
    return nullspace(equations, N)


def projective_normalize(v: list[int]) -> tuple[int, ...] | None:
    pivot = next((x for x in v if x), None)
    if pivot is None:
        return None
    scale = inv(pivot)
    return tuple(scale * x % P for x in v)


def deviation_direction_count(
    cores: tuple[tuple[int, ...], ...], basis: list[list[int]] | None = None
) -> int:
    """Exact row-matroid ceiling for every possible choice of stack rows in W.

    Proportional defect functionals always induce the same scalar ratio, for all
    u0,u1 in W.  Hence their number of nonzero projective directions is an exact,
    choice-free upper bound on the number of induced finite gammas.
    """
    if basis is None:
        basis = core_family_basis(cores)
    directions = set()
    for core in cores:
        for delta in DEFECTS[core].values():
            direction = projective_normalize([dot(delta, w) for w in basis])
            if direction is not None:
                directions.add(direction)
    return len(directions)


def induced_gammas(
    cores: tuple[tuple[int, ...], ...], u0: list[int], u1: list[int]
) -> dict[int, list[tuple[tuple[int, ...], int]]]:
    out: dict[int, list[tuple[tuple[int, ...], int]]] = {}
    for core in cores:
        for i, delta in DEFECTS[core].items():
            a = dot(delta, u0)
            b = dot(delta, u1)
            if b == 0:
                continue
            gamma = -a * inv(b) % P
            out.setdefault(gamma, []).append((core, i))
    return out


def verify_induced(
    gammas: dict[int, list[tuple[tuple[int, ...], int]]], u0: list[int], u1: list[int]
) -> None:
    for gamma, witnesses in gammas.items():
        word = [(a + gamma * b) % P for a, b in zip(u0, u1)]
        for core, i in witnesses:
            support = core + (i,)
            assert len(set(support)) == T
            assert dot(DEFECTS[core][i], word) == 0
            assert dot(DEFECTS[core][i], u1) != 0
            # The core constraints plus the external zero defect say that one
            # degree-<K interpolant agrees on all T positions.  The nonzero u1
            # defect says the pair cannot jointly agree there.


@dataclass
class Hit:
    count: int
    quotient_dim: int
    cores: tuple[tuple[int, ...], ...]
    u0: list[int]
    u1: list[int]
    gammas: dict[int, list[tuple[tuple[int, ...], int]]]


def optimize_rows(
    cores: tuple[tuple[int, ...], ...], rng: random.Random, trials: int
) -> Hit | None:
    basis = core_family_basis(cores)
    qdim = len(basis) - K
    if qdim < 2:
        return None
    best: Hit | None = None
    # Coordinate basis pairs catch sparse spline directions; random pairs catch
    # generic projections of larger quotient spaces.
    pairs: list[tuple[list[int], list[int]]] = []
    for a in range(len(basis)):
        for b in range(a + 1, len(basis)):
            ca = [0] * len(basis)
            cb = [0] * len(basis)
            ca[a] = 1
            cb[b] = 1
            pairs.append((ca, cb))
    for _ in range(trials):
        pairs.append(
            (
                [rng.randrange(P) for _ in basis],
                [rng.randrange(P) for _ in basis],
            )
        )
    for ca, cb in pairs:
        u0 = word_from_coeffs(basis, ca)
        u1 = word_from_coeffs(basis, cb)
        gs = induced_gammas(cores, u0, u1)
        if best is None or len(gs) > best.count:
            verify_induced(gs, u0, u1)
            best = Hit(len(gs), qdim, cores, u0, u1, gs)
    return best


def better(a: Hit | None, b: Hit | None) -> Hit | None:
    if a is None:
        return b
    if b is None:
        return a
    return b if b.count > a.count else a


def main() -> None:
    rng = random.Random(20260709)
    left = tuple(range(8))
    right = tuple(range(8, 16))
    anchor = (left, right)

    baseline = optimize_rows(anchor, rng, trials=200)
    assert baseline is not None
    print(f"p={P}, omega={OMEGA}, mu16={XS}")
    print(
        "two-core baseline:",
        f"count={baseline.count}",
        f"qdim={baseline.quotient_dim}",
        f"direction_ceiling={deviation_direction_count(anchor)}",
    )

    best: Hit | None = baseline
    top: list[Hit] = []
    admissible = 0
    direction_ceiling3 = 0
    for third in ALL_CORES:
        if third in anchor:
            continue
        hit = optimize_rows(anchor + (third,), rng, trials=24)
        if hit is None:
            continue
        admissible += 1
        direction_ceiling3 = max(direction_ceiling3, deviation_direction_count(hit.cores))
        top.append(hit)
        best = better(best, hit)
    top.sort(key=lambda h: (h.count, h.quotient_dim), reverse=True)
    top = top[:20]
    print(f"admissible third cores with dim(W/RS)>=2: {admissible}")
    print(f"exact maximum projective-defect ceiling over those triples: {direction_ceiling3}")
    print("top triple counts:", [(h.count, h.quotient_dim, h.cores[-1]) for h in top[:10]])

    # Exhaust a fourth core only from the most promising triple families.
    best4: Hit | None = None
    admissible4 = 0
    direction_ceiling4 = 0
    for seed in top[:8]:
        for fourth in ALL_CORES:
            if fourth in seed.cores:
                continue
            hit = optimize_rows(seed.cores + (fourth,), rng, trials=12)
            if hit is None:
                continue
            admissible4 += 1
            direction_ceiling4 = max(direction_ceiling4, deviation_direction_count(hit.cores))
            best4 = better(best4, hit)
            best = better(best, hit)
    print(f"admissible fourth-core extensions searched: {admissible4}")
    print(f"maximum projective-defect ceiling in those extensions: {direction_ceiling4}")
    if best4 is not None:
        print(
            "best fourth-core extension:",
            f"count={best4.count}",
            f"qdim={best4.quotient_dim}",
            f"cores={best4.cores}",
        )

    # The complementary consecutive anchor is only one orbit of core pairs.
    # Stress arbitrary overlap patterns, biasing the third core toward a small
    # mutation of one anchor (the regime where compatibility most often leaves
    # at least two non-global spline directions).
    random_best: Hit | None = None
    random_admissible = 0
    random_direction_ceiling = 0
    for _ in range(6000):
        first, second = rng.sample(ALL_CORES, 2)
        base = first if rng.randrange(2) == 0 else second
        swaps = 1 if rng.random() < 0.7 else 2
        removed = rng.sample(list(base), swaps)
        added = rng.sample([i for i in range(N) if i not in base], swaps)
        third = tuple(sorted((set(base) - set(removed)) | set(added)))
        if third == first or third == second:
            continue
        hit = optimize_rows((first, second, third), rng, trials=8)
        if hit is None:
            continue
        random_admissible += 1
        random_direction_ceiling = max(
            random_direction_ceiling, deviation_direction_count(hit.cores)
        )
        random_best = better(random_best, hit)
        best = better(best, hit)
    print(f"admissible random/mutated triples: {random_admissible}")
    print(f"maximum projective-defect ceiling in random sample: {random_direction_ceiling}")
    if random_best is not None:
        print(
            "best random/mutated triple:",
            f"count={random_best.count}",
            f"qdim={random_best.quotient_dim}",
            f"cores={random_best.cores}",
        )

    assert best is not None
    print("BEST")
    print(f"  count={best.count} (target counterexample: > {N})")
    print(f"  quotient_dim={best.quotient_dim}")
    print(f"  cores={best.cores}")
    print(f"  u0={best.u0}")
    print(f"  u1={best.u1}")
    print(f"  gammas={sorted(best.gammas)}")
    multiplicities = sorted((len(v) for v in best.gammas.values()), reverse=True)
    print(f"  witness multiplicities={multiplicities}")


if __name__ == "__main__":
    main()
