#!/usr/bin/env python3
"""#466 R172: high-order stress for the closed-form dyadic tail law.

R170 found that N(T) <= (3/4) M exp(-T/4) on the 0.5-grid was enough to imply
the R168 MGF budget and survived n<=128.  This probe tests larger dyadic orders
where exact coset spectra are still feasible.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    is_prime,
    subgroup,
)
from scripts.probes.probe_r169_finite_grid_mgf_certificate import certificate_ratio  # noqa: E402


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def tail_worst(xs: list[float], step: float = 0.5) -> tuple[float, float, int]:
    m = len(xs)
    best = (0.0, 0.0, 0)
    k = 2  # T >= 1
    while k * step <= max(xs) + step:
        t = k * step
        count = sum(1 for x in xs if x >= t)
        denom = 0.75 * m * math.exp(-0.25 * t)
        ratio = count / denom if denom else float("inf")
        if ratio > best[0]:
            best = (ratio, t, count)
        k += 1
    return best


def main() -> None:
    cases: list[tuple[int, int, str]] = []
    for n, starts_counts in [
        (256, [(256**2, 5), (256**3, 4)]),
        (512, [(512**2, 4)]),
    ]:
        for start, count in starts_counts:
            for p in next_primes_congruent_one(n, start, count):
                cases.append((n, p, f"start={start}"))

    print("n    p          cosets    maxX     tail_ratio T     count   grid0.5 mgf")
    print("-" * 88)
    worst_tail = (0.0, None)
    worst_grid = (0.0, None)
    violations = 0
    for n, p, label in cases:
        xs = normalized_values(p, n)
        ratio, t, count = tail_worst(xs)
        grid_ratio, mgf = certificate_ratio(xs, 0.5, math.ceil(max(xs) + 1))
        if ratio > 1 + 1e-9:
            violations += 1
        if ratio > worst_tail[0]:
            worst_tail = (ratio, (n, p, t, count, label))
        if grid_ratio > worst_grid[0]:
            worst_grid = (grid_ratio, (n, p, label))
        print(
            f"{n:<4d} {p:<10d} {len(xs):<9d} {max(xs):<8.3f} "
            f"{ratio:<10.6f} {t:<5g} {count:<7d} {grid_ratio:<7.5f} {mgf:.5f}"
        )

    print("\nsummary")
    n, p, t, count, label = worst_tail[1]
    print(f"worst_tail ratio={worst_tail[0]:.6f} n={n} p={p} T={t} count={count} {label}")
    n, p, label = worst_grid[1]
    print(f"worst_grid ratio={worst_grid[0]:.6f} n={n} p={p} {label}")
    print(f"tail_violations={violations}")


if __name__ == "__main__":
    main()
