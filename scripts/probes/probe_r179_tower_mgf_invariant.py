#!/usr/bin/env python3
"""#466 R179: R168 MGF invariant along one dyadic tower.

R178 showed the distribution is nearly invariant under n -> 2n at fixed p.
This probe computes the R168 MGF, the finite-grid certificate, and coarse bin
masses for all dyadic subgroup orders inside the same prime field.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    first_prime_congruent_one,
    subgroup,
)
from scripts.probes.probe_r169_finite_grid_mgf_certificate import certificate_ratio  # noqa: E402


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def stats(xs: list[float]) -> dict[str, float]:
    m = len(xs)
    mgf = sum(math.exp(x / 8) for x in xs) / m
    grid, _ = certificate_ratio(xs, 0.5, math.ceil(max(xs) + 1))
    return {
        "mgf": mgf,
        "grid": grid,
        "low": sum(1 for x in xs if x < 0.5) / m,
        "s1": sum(1 for x in xs if x >= 1) / m,
        "s4": sum(1 for x in xs if x >= 4) / m,
        "max": max(xs),
    }


def main() -> None:
    # Interactive default: order 128 is enough to test the invariant without
    # enumerating millions of small-order cosets.  Pass a larger max order as
    # argv[1] for an expensive stress run.
    max_order = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    p = first_prime_congruent_one(max_order, max(max_order**2, 100_000))
    print(f"tower prime p={p}")
    print("n    cosets    mgf       grid0.5   low<0.5  S1       S4       maxX")
    print("-" * 82)
    previous = None
    n = 8
    orders = []
    while n <= max_order:
        orders.append(n)
        n *= 2
    for n in orders:
        xs = normalized_values(p, n)
        st = stats(xs)
        delta = "" if previous is None else f" dMGF={st['mgf'] - previous:+.6f}"
        previous = st["mgf"]
        print(
            f"{n:<4d} {len(xs):<9d} {st['mgf']:<9.6f} {st['grid']:<9.6f} "
            f"{st['low']:<8.4f} {st['s1']:<8.4f} {st['s4']:<8.4f} {st['max']:<8.3f}{delta}"
        )


if __name__ == "__main__":
    main()
