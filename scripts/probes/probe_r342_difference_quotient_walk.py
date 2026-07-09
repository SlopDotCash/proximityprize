#!/usr/bin/env python3
"""Probe multiplicative mixing of the quotient classes of H - 1."""

from collections import Counter
from math import ceil, log


def factor(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // ell, p) != 1 for ell in fs):
            return g
    raise RuntimeError("no primitive root")


def convolve(a, b, m):
    c = Counter()
    for x, vx in a.items():
        for y, vy in b.items():
            c[(x + y) % m] += vx * vy
    return c


def run(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    logs = [0] * p
    x = 1
    for e in range(p - 1):
        logs[x] = e
        x = x * g % p
    hgen = pow(g, m, p)
    h = 1
    step = Counter()
    for _ in range(n):
        if h != 1:
            step[logs[(h - 1) % p] % m] += 1
        h = h * hgen % p
    k = ceil(log(m, n - 1))
    walk = Counter({0: 1})
    rows = []
    for depth in range(1, 13):
        walk = convolve(walk, step, m)
        total = (n - 1) ** depth
        support = len(walk)
        l2_ratio = m * sum(v * v for v in walk.values()) / (total * total)
        max_ratio = m * max(walk.values()) / total
        rows.append((depth, support, l2_ratio, max_ratio))
    print(f"p={p} n={n} m={m} k={k} atoms={len(step)} max_atom={max(step.values())}")
    for depth, support, l2_ratio, max_ratio in rows:
        print(f"  d={depth} support={support}/{m} L2/unif={l2_ratio:.6g} Linf/unif={max_ratio:.6g}")


if __name__ == "__main__":
    for cell in [(521, 8), (100049, 8), (1048609, 16), (16777601, 32)]:
        run(*cell)
