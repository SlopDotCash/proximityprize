#!/usr/bin/env python3
"""#466 R206: random coset sampling at the actual prize quotient index.

The exact sweep probes can enumerate all cosets only for moderate
M = (p - 1) / n.  The prize regime has M around 2^128.  This probe samples
random nonzero frequencies b for primes

    p = M*n + 1,      M >= 2^128,

with dyadic n, and measures the normalized Gauss-period spectrum

    X_b = |sum_{h in μ_n} exp(2πi b h / p)|^2 / n.

The output stress-tests the R189/R203 large-index hypotheses in the actual
huge-index regime: quarter-MGF, max sample value, and empirical tail excess
against N(T) <= 0.6 S exp(-T/2) + 2 over the sampled population size S.
"""

from __future__ import annotations

import argparse
import math
import random
from typing import Iterable

import sympy as sp


def next_prime_congruent_one(n: int, min_index: int) -> tuple[int, int]:
    """Return (p, M) with p = M*n + 1 prime and M >= min_index."""
    m = min_index
    while True:
        p = m * n + 1
        if sp.isprime(p):
            return p, m
        m += 1


def element_of_order_n(p: int, n: int, rng: random.Random) -> int:
    cofactor = (p - 1) // n
    while True:
        a = rng.randrange(2, p - 1)
        z = pow(a, cofactor, p)
        if z != 1 and pow(z, n, p) == 1 and pow(z, n // 2, p) != 1:
            return z


def subgroup_from_generator(z: int, p: int, n: int) -> list[int]:
    h = []
    x = 1
    for _ in range(n):
        h.append(x)
        x = (x * z) % p
    return h


def normalized_samples(p: int, n: int, samples: int, seed: int) -> list[float]:
    rng = random.Random(seed)
    z = element_of_order_n(p, n, rng)
    h = subgroup_from_generator(z, p, n)
    scale = 2.0 * math.pi / p
    xs = []
    for _ in range(samples):
        b = rng.randrange(1, p)
        real = 0.0
        imag = 0.0
        for x in h:
            angle = ((b * x) % p) * scale
            real += math.cos(angle)
            imag += math.sin(angle)
        xs.append((real * real + imag * imag) / n)
    return xs


def mgf(xs: Iterable[float], rate: float) -> float:
    vals = list(xs)
    return sum(math.exp(rate * x) for x in vals) / len(vals)


def tail_excess(xs: list[float], c_bulk: float, spike_budget: float, step: float) -> tuple[float, float, int]:
    max_x = max(xs)
    worst_excess = -1e100
    worst_theta = 0.0
    worst_count = 0
    j = 2
    while j * step <= max_x + 1e-12:
        theta = j * step
        count = sum(1 for x in xs if theta <= x)
        bound = c_bulk * len(xs) * math.exp(-theta / 2) + spike_budget
        excess = count - bound
        if excess > worst_excess:
            worst_excess = excess
            worst_theta = theta
            worst_count = count
        j += 1
    return worst_excess, worst_theta, worst_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--samples", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=466206)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    args = parser.parse_args()

    min_index = 2 ** args.min_index_power
    rows = []
    for offset, n in enumerate(args.ns):
        p, m = next_prime_congruent_one(n, min_index)
        xs = normalized_samples(p, n, args.samples, args.seed + offset)
        excess, theta, count = tail_excess(xs, args.c_bulk, args.spike_budget, args.step)
        rows.append(
            (
                mgf(xs, 1 / 4),
                max(xs),
                excess,
                theta,
                count,
                sum(xs) / len(xs),
                m,
                n,
                p,
            )
        )

    rows.sort(reverse=True)
    print(
        f"R206 prize-index random sampling samples={args.samples} "
        f"min_index=2^{args.min_index_power}"
    )
    print("mgf1/4  maxX    meanX   excess@T,count  M_offset  n     p")
    print("-" * 110)
    for mgf4, max_x, excess, theta, count, mean_x, m, n, p in rows:
        print(
            f"{mgf4:<7.4f} {max_x:<7.3f} {mean_x:<7.4f} "
            f"{excess:>8.3f}@{theta:<4.1f},{count:<5d} "
            f"{m - min_index:<8d} {n:<5d} {p}"
        )

    print("\nsummary")
    print(f"max_positive_excess={max([r[2] for r in rows if r[2] > 0], default=0.0):.6f}")
    worst_mgf = max(rows, key=lambda r: r[0])
    worst_max = max(rows, key=lambda r: r[1])
    print(f"worst_mgf={worst_mgf[0]:.6f} n={worst_mgf[7]} M_offset={worst_mgf[6] - min_index}")
    print(f"worst_maxX={worst_max[1]:.6f} n={worst_max[7]} M_offset={worst_max[6] - min_index}")


if __name__ == "__main__":
    main()
