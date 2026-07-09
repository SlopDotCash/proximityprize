#!/usr/bin/env python3
"""R349: antipodal-orientation higher-energy probe.

For H = mu_n and a transversal A of H/{+1,-1}, enumerate every orientation
A_eps = {eps_a a}.  The Gauss period of H is twice the real part of the
Fourier sum of every A_eps.  Hence an orientation-averaged Wick bound would
give the desired bound for H, up to a harmless factor two.

This probe uses exact integer convolution.  It reports full-set and averaged
half-set energies relative to their Gaussian Wick envelopes.
"""

from __future__ import annotations

import argparse
import itertools
import math


def prime_factors(n: int) -> list[int]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            factors.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        factors.append(n)
    return factors


def primitive_root(p: int) -> int:
    factors = prime_factors(p - 1)
    return next(
        g for g in range(2, p)
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors)
    )


def subgroup(p: int, n: int) -> list[int]:
    if (p - 1) % n != 0:
        raise ValueError("n must divide p - 1")
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    return sorted({pow(step, j, p) for j in range(n)})


def antipodal_transversal(h: list[int], p: int) -> list[int]:
    seen: set[int] = set()
    reps: list[int] = []
    for x in h:
        if x not in seen:
            reps.append(x)
            seen.update((x, (-x) % p))
    return reps


def energy(a: list[int], p: int, depth: int) -> int:
    counts = {0: 1}
    for _ in range(depth):
        next_counts: dict[int, int] = {}
        for total, multiplicity in counts.items():
            for x in a:
                residue = (total + x) % p
                next_counts[residue] = next_counts.get(residue, 0) + multiplicity
        counts = next_counts
    return sum(multiplicity * multiplicity for multiplicity in counts.values())


def odd_double_factorial(depth: int) -> int:
    return math.prod(range(1, 2 * depth, 2))


def run_cell(p: int, n: int, max_depth: int) -> None:
    h = subgroup(p, n)
    reps = antipodal_transversal(h, p)
    orientations = list(itertools.product((-1, 1), repeat=len(reps)))
    print(f"p={p} n={n} orientations={len(orientations)}")
    for depth in range(2, max_depth + 1):
        full_energy = energy(h, p, depth)
        oriented = [
            energy([(sign * x) % p for sign, x in zip(signs, reps)], p, depth)
            for signs in orientations
        ]
        average = sum(oriented) / len(oriented)
        wick_full = odd_double_factorial(depth) * n**depth
        wick_half = odd_double_factorial(depth) * (n // 2) ** depth
        print(
            f"  k={depth}: H/W={full_energy / wick_full:.8f} "
            f"avg(A_eps)/W_half={average / wick_half:.8f} "
            f"4^k avg/H={4**depth * average / full_energy:.8f} "
            f"range=[{min(oriented)},{max(oriented)}]"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=6)
    args = parser.parse_args()
    for p, n in ((521, 8), (100049, 8), (65537, 16)):
        run_cell(p, n, args.max_depth)


if __name__ == "__main__":
    main()
