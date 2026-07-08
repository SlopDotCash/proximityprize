#!/usr/bin/env python3
"""#466 R180: multi-prime stress for the dyadic tower MGF invariant."""

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


def stats(xs: list[float]) -> tuple[float, float, float, float, float]:
    m = len(xs)
    mgf = sum(math.exp(x / 8) for x in xs) / m
    grid, _ = certificate_ratio(xs, 0.5, math.ceil(max(xs) + 1))
    low = sum(1 for x in xs if x < 0.5) / m
    s1 = sum(1 for x in xs if x >= 1) / m
    s4 = sum(1 for x in xs if x >= 4) / m
    return mgf, grid, low, s1, s4


def main() -> None:
    primes = next_primes_congruent_one(512, 512**2, 6)
    orders = (16, 32, 64, 128, 256, 512)
    print("p          minMGF   maxMGF   span     maxGrid  minLow  maxS1   maxS4")
    print("-" * 86)
    worst = (0.0, None)
    for p in primes:
        rows = []
        for n in orders:
            rows.append((n, *stats(normalized_values(p, n))))
        mgfs = [r[1] for r in rows]
        grids = [r[2] for r in rows]
        lows = [r[3] for r in rows]
        s1s = [r[4] for r in rows]
        s4s = [r[5] for r in rows]
        span = max(mgfs) - min(mgfs)
        if span > worst[0]:
            worst = (span, p)
        print(
            f"{p:<10d} {min(mgfs):<8.6f} {max(mgfs):<8.6f} {span:<8.6f} "
            f"{max(grids):<8.6f} {min(lows):<7.4f} {max(s1s):<7.4f} {max(s4s):.4f}"
        )
        print("  " + " ".join(f"n={n}:M={mgf:.5f},G={grid:.5f}" for n, mgf, grid, *_ in rows))
    print("\nsummary")
    print(f"worst_mgf_span={worst[0]:.6f} at p={worst[1]}")


if __name__ == "__main__":
    main()
