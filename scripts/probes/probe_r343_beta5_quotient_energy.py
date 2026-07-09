#!/usr/bin/env python3
"""Exact critical-depth H-1 quotient energy at p approximately n^5."""

from collections import Counter
from math import ceil, isqrt, log

from probe_r342_difference_quotient_walk import factor, primitive_root


def bsgs_many(base, values, order, p):
    width = isqrt(order) + 1
    baby = {}
    x = 1
    for j in range(width):
        baby.setdefault(x, j)
        x = x * base % p
    jump = pow(pow(base, width, p), -1, p)
    answers = {}
    for value in values:
        y = value
        for i in range(width + 1):
            j = baby.get(y)
            if j is not None:
                e = i * width + j
                if e < order:
                    answers[value] = e
                    break
            y = y * jump % p
        else:
            raise RuntimeError(f"discrete log failed for {value}")
    return answers


def convolve_step(walk, step, modulus):
    out = Counter()
    for x, vx in walk.items():
        for y, vy in step.items():
            out[(x + y) % modulus] += vx * vy
    return out


def run(p, n):
    assert (p - 1) % n == 0
    g = primitive_root(p)
    m = (p - 1) // n
    hgen = pow(g, m, p)
    differences = []
    h = 1
    for _ in range(n):
        if h != 1:
            differences.append((h - 1) % p)
        h = h * hgen % p
    base = pow(g, n, p)
    powered = {pow(x, n, p) for x in differences}
    logs = bsgs_many(base, powered, m, p)
    step = Counter(logs[pow(x, n, p)] for x in differences)
    depth = ceil(log(m, n - 1))
    walk = Counter({0: 1})
    print(f"p={p} n={n} m={m} beta={log(p,n):.6f} depth={depth} "
          f"atoms={len(step)} max_atom={max(step.values())}", flush=True)
    for d in range(1, depth + 1):
        walk = convolve_step(walk, step, m)
        total = (n - 1) ** d
        energy = sum(v * v for v in walk.values())
        l2_ratio = m * energy / (total * total)
        linf_ratio = m * max(walk.values()) / total
        diagonal_ratio = m / total
        print(f"  d={d} support={len(walk)}/{m} L2/unif={l2_ratio:.8g} "
              f"Linf/unif={linf_ratio:.8g} m/(n-1)^d={diagonal_ratio:.8g}", flush=True)


if __name__ == "__main__":
    for cell in ((1_073_741_953, 64), (34_359_740_801, 128)):
        run(*cell)
