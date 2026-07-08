#!/usr/bin/env python3
"""#466 R183: measure the R182 tower product-budget input.

R182 reduced a tower-step MGF certificate to

    avg_i exp(left_i/8) * exp(right_i/8) <= 2.

This probe computes that exact product budget for dyadic tower splits across
several shared primes.
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


def step_budget(p: int, n: int) -> tuple[float, float, float, float]:
    child = periods(p, n)
    parent = periods(p, 2 * n)
    sig_child = mean_sq(child)
    sig_parent = mean_sq(parent)
    k = (p - 1) // (2 * n)
    product_terms = []
    parent_terms = []
    energy_terms = []
    for j, z in enumerate(parent):
        left = abs(child[j]) ** 2 / sig_child
        right = abs(child[j + k]) ** 2 / sig_child
        parent_x = abs(z) ** 2 / sig_parent
        product_terms.append(math.exp(left / 8) * math.exp(right / 8))
        parent_terms.append(math.exp(parent_x / 8))
        energy_terms.append(math.exp((left + right) / 8))
    return (
        sum(parent_terms) / len(parent_terms),
        sum(product_terms) / len(product_terms),
        max(product_terms),
        sig_parent / sig_child,
    )


def main() -> None:
    primes = next_primes_congruent_one(512, 512**2, 6)
    print("p          step     parentMGF productBudget maxTerm sigmaRatio")
    print("-" * 78)
    worst = (0.0, None)
    for p in primes:
        for n in (16, 32, 64, 128, 256):
            parent, product, max_term, sigma_ratio = step_budget(p, n)
            if product > worst[0]:
                worst = (product, (p, n))
            print(
                f"{p:<10d} {n:<3d}->{2*n:<3d} {parent:<9.6f} "
                f"{product:<13.6f} {max_term:<7.3f} {sigma_ratio:.5f}"
            )
    print("\nsummary")
    print(f"worst_product_budget={worst[0]:.6f} at p={worst[1][0]} step={worst[1][1]}->{2*worst[1][1]}")
    print("target <= 2.0")


if __name__ == "__main__":
    main()
