#!/usr/bin/env python3
"""#466 R66: fit dyadic coset tail-count envelopes.

R65 suggested replacing false moment-ratio monotonicity with an
order-statistic theorem for X_b = |η_b|^2 / σ^2.  This probe measures the
tail counts N(T) = #{cosets : X_b >= T} against exponential envelopes.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    subgroup,
)


THRESHOLDS = [1.5, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 28]


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def counts(xs: list[float]) -> list[int]:
    return [sum(1 for x in xs if x >= t) for t in THRESHOLDS]


def best_alpha(cosets: int, ts: list[int], ns: list[int]) -> float:
    """Largest alpha such that ns <= cosets * exp(-alpha*T) for all nonzero ns."""
    vals = []
    for t, count in zip(ts, ns, strict=True):
        if count > 0:
            vals.append(math.log(cosets / count) / t)
    return min(vals) if vals else float("inf")


def main() -> None:
    cases = [
        (32, 32993, "spike"),
        (32, 1048609, "control"),
        (64, 264769, "spike"),
        (64, 16778497, "spike"),
        (64, 16777601, "control"),
        (128, 2101249, "small-spike"),
        (128, 268437889, "control"),
        (256, 16777729, "control"),
    ]
    print("n   p          kind        cosets    alpha  maxX")
    print("-" * 70)
    for n, p, kind in cases:
        xs = normalized_values(p, n)
        ns = counts(xs)
        alpha = best_alpha(len(xs), THRESHOLDS, ns)
        print(f"{n:<3d} {p:<10d} {kind:<11s} {len(xs):<9d} {alpha:<6.4f} {max(xs):.4f}")
        print("  " + " ".join(f"N{t}={c}" for t, c in zip(THRESHOLDS, ns, strict=True)))
        for a in (0.25, 0.20, 0.18, 0.16):
            bad = [
                (t, c, len(xs) * math.exp(-a * t))
                for t, c in zip(THRESHOLDS, ns, strict=True)
                if c > len(xs) * math.exp(-a * t) + 1e-9
            ]
            print(f"  exp(-{a:.2f}T) violations={len(bad)}" + ("" if not bad else f" first={bad[0]}"))

    print("\nstress summary for exp(-T/4)")
    from scripts.probes.probe_r63_dyadic_prime_sensitivity import next_primes_congruent_one

    stress = []
    for n, start, count in [(32, 32**3, 8), (32, 32**4, 8), (64, 64**3, 8), (64, 64**4, 5)]:
        for p in next_primes_congruent_one(n, start, count):
            xs = normalized_values(p, n)
            ns = counts(xs)
            worst = max(
                c / (len(xs) * math.exp(-0.25 * t))
                for t, c in zip(THRESHOLDS, ns, strict=True)
            )
            stress.append((worst, n, p))
    stress.sort(reverse=True)
    for worst, n, p in stress[:8]:
        print(f"  n={n} p={p} worst_ratio={worst:.4f}")


if __name__ == "__main__":
    main()
