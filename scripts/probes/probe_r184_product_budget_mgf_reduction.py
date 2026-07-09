#!/usr/bin/env python3
"""#466 R184: reduce tower product budget to one-level MGF bounds?

R183 measured the paired child product budget
    avg exp(left/8) exp(right/8).
This probe compares it to child MGFs at higher rates and Cauchy-style
envelopes, looking for a simpler inductive invariant.
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    is_prime,
    primitive_root,
)


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def periods(p: int, order: int) -> list[complex]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // order, p)
    zeta = cmath.exp(2j * math.pi / p)
    vals = []
    for j in range((p - 1) // order):
        b = pow(g, j, p)
        x = 1
        s = 0j
        for _ in range(order):
            s += zeta ** ((b * x) % p)
            x = (x * step) % p
        vals.append(s)
    return vals


def mean_sq(vals: list[complex]) -> float:
    return sum(abs(z) ** 2 for z in vals) / len(vals)


def step_stats(p: int, n: int) -> tuple[float, float, float, float, float]:
    child = periods(p, n)
    sig = mean_sq(child)
    x = [abs(z) ** 2 / sig for z in child]
    k = (p - 1) // (2 * n)
    pairs = [(x[j], x[j + k]) for j in range(k)]
    product = sum(math.exp(a / 8) * math.exp(b / 8) for a, b in pairs) / len(pairs)
    mgf8 = sum(math.exp(v / 8) for v in x) / len(x)
    mgf6 = sum(math.exp(v / 6) for v in x) / len(x)
    mgf4 = sum(math.exp(v / 4) for v in x) / len(x)
    cauchy = math.sqrt(
        (sum(math.exp(a / 4) for a, _ in pairs) / len(pairs))
        * (sum(math.exp(b / 4) for _, b in pairs) / len(pairs))
    )
    return product, mgf8, mgf6, mgf4, cauchy


def main() -> None:
    primes = next_primes_congruent_one(512, 512**2, 6)
    print("p          step     product  mgf1/8  mgf1/6  mgf1/4  cauchy  prod/mgf1/4")
    print("-" * 92)
    worst = (0.0, None)
    for p in primes:
        for n in (16, 32, 64, 128, 256):
            product, mgf8, mgf6, mgf4, cauchy = step_stats(p, n)
            ratio = product / mgf4
            if ratio > worst[0]:
                worst = (ratio, (p, n, product, mgf4))
            print(
                f"{p:<10d} {n:<3d}->{2*n:<3d} {product:<8.5f} {mgf8:<7.5f} "
                f"{mgf6:<7.5f} {mgf4:<7.5f} {cauchy:<7.5f} {ratio:.5f}"
            )
    print("\nsummary")
    p, n, product, mgf4 = worst[1]
    print(f"worst product/mgf1/4={worst[0]:.6f} at p={p} step={n}->{2*n} product={product:.6f} mgf1/4={mgf4:.6f}")


if __name__ == "__main__":
    main()
