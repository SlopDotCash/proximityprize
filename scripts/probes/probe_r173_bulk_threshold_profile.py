#!/usr/bin/env python3
"""#466 R173: bulk threshold profile near T=1.

R170/R172 showed the closed-form grid tail law is limited by the bulk
threshold T=1, not by exceptional high-tail cosets.  This probe measures the
normalized coset magnitude distribution near T=1 and compares it with the
candidate envelope (3/4) exp(-T/4).
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
    return sorted((m / sigma2 for m in mags))


def quantile(xs: list[float], q: float) -> float:
    if not xs:
        return float("nan")
    idx = min(len(xs) - 1, max(0, round(q * (len(xs) - 1))))
    return xs[idx]


def main() -> None:
    thresholds = [0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2.0]
    cases = [
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
        (512, 262657, "high-order"),
    ]
    cases.extend((32, p, "n32-n4") for p in next_primes_congruent_one(32, 32**4, 4))
    cases.extend((64, p, "n64-n4") for p in next_primes_congruent_one(64, 64**4, 4))

    print("n   p          kind        q50    q67    q75    q90    maxX")
    print("-" * 78)
    worst = (0.0, None)
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        m = len(xs)
        print(
            f"{n:<3d} {p:<10d} {kind:<11s} "
            f"{quantile(xs,0.50):<6.3f} {quantile(xs,0.67):<6.3f} "
            f"{quantile(xs,0.75):<6.3f} {quantile(xs,0.90):<6.3f} {xs[-1]:.3f}"
        )
        ratios = []
        for t in thresholds:
            frac = sum(1 for x in xs if x >= t) / m
            env = 0.75 * math.exp(-0.25 * t)
            ratios.append((t, frac, env, frac / env))
            if frac / env > worst[0]:
                worst = (frac / env, (n, p, kind, t, frac, env))
        print("  " + " ".join(f"T{t:g}:{frac:.3f}/{env:.3f}({ratio:.3f})" for t, frac, env, ratio in ratios))

    print("\nsummary")
    ratio, (n, p, kind, t, frac, env) = worst
    print(f"worst_bulk_ratio={ratio:.6f} n={n} p={p} kind={kind} T={t} frac={frac:.6f} env={env:.6f}")


if __name__ == "__main__":
    main()
