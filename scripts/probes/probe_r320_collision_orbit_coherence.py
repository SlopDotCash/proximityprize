#!/usr/bin/env python3
"""#466 R320: compare relation-orbit coherence in resonant and generic cells.

Build the exact characteristic-zero shadow histogram at depth r, push it to
F_p, and aggregate off-diagonal collision mass by the signed cyclic-shift orbit
of the difference vector.  This tests whether super-Wick mass is distinguished
by concentration in a small number of recurrent relation templates.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict

import sympy as sp

from probe_r307_binomial_norm_depth3 import order_n_element


def shadow_histogram(n: int, r: int) -> Counter[tuple[int, ...]]:
    m = n // 2
    steps = []
    for j in range(n):
        vec = [0] * m
        if j < m:
            vec[j] = 1
        else:
            vec[j - m] = -1
        steps.append(tuple(vec))
    hist = Counter({(0,) * m: 1})
    for _ in range(r):
        nxt: Counter[tuple[int, ...]] = Counter()
        for vec, count in hist.items():
            for step in steps:
                nxt[tuple(a + b for a, b in zip(vec, step))] += count
        hist = nxt
    return hist


def shift(vec: tuple[int, ...], amount: int, n: int) -> tuple[int, ...]:
    m = n // 2
    out = [0] * m
    for j, coeff in enumerate(vec):
        k = (j + amount) % n
        if k >= m:
            out[k - m] -= coeff
        else:
            out[k] += coeff
    return tuple(out)


def orbit_key(vec: tuple[int, ...], n: int) -> tuple[int, ...]:
    neg = tuple(-x for x in vec)
    return min(*(shift(vec, s, n) for s in range(n)), *(shift(neg, s, n) for s in range(n)))


def analyze(n: int, p: int, r: int, top: int) -> None:
    hist = shadow_histogram(n, r)
    g = order_n_element(p, n)
    powers = []
    x = 1
    for _ in range(n // 2):
        powers.append(x)
        x = x * g % p
    fibers: dict[int, list[tuple[tuple[int, ...], int]]] = defaultdict(list)
    for vec, count in hist.items():
        value = sum(a * b for a, b in zip(vec, powers)) % p
        fibers[value].append((vec, count))

    orbit_mass: Counter[tuple[int, ...]] = Counter()
    total = 0
    pair_count = 0
    for fiber in fibers.values():
        for i, (left, wl) in enumerate(fiber):
            for right, wr in fiber[i + 1 :]:
                mass = 2 * wl * wr
                diff = tuple(a - b for a, b in zip(left, right))
                orbit_mass[orbit_key(diff, n)] += mass
                total += mass
                pair_count += 1
    ranked = orbit_mass.most_common(top)
    print(
        f"n={n} p={p} r={r} shadow_keys={len(hist)} collision_pairs={pair_count} "
        f"orbits={len(orbit_mass)} collision_mass={total}"
    )
    cumulative = 0
    for rank, (key, mass) in enumerate(ranked, 1):
        cumulative += mass
        support = sum(value != 0 for value in key)
        l1 = sum(abs(value) for value in key)
        print(
            f"  rank={rank} mass={mass} share={mass / total:.9f} "
            f"cumulative={cumulative / total:.9f} support={support} l1={l1} relation={key}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=8)
    args = parser.parse_args()
    print("# R320 collision-orbit coherence")
    analyze(32, 21523361, 3, args.top)
    analyze(32, 1439393, 4, args.top)
    x = sp.symbols("x")
    f = 2 + x + x**4 + x**8 + x**12
    h = (1 + x) * x**4 - x - 3
    reduced = sp.rem((x**4 - 1) * f, x**16 + 1, domain=sp.ZZ)
    resultant = int(sp.resultant(x**16 + 1, h, x))
    assert sp.expand(reduced - h) == 0
    assert resultant == 2**5 * 1439393
    print(f"primitive_class reduced_identity={reduced} resultant={resultant}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
