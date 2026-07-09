#!/usr/bin/env python3
"""#466 R183: child-pair angle equidistribution in the dyadic tower.

R180 explains the observed split constants by the real-Gaussian fixed point.
The proof-facing statement is angle equidistribution of child period pairs

  (eta_n(C0), eta_n(C1)) / sqrt(eta_n(C0)^2 + eta_n(C1)^2).

This probe measures low Fourier coefficients and coarse arc discrepancy of
those angles at same-prime dyadic tower steps.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import (  # noqa: E402
    period_by_coset_index,
)
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    first_prime_congruent_one,
)


def angle_stats(p: int, n: int, bins: int = 16) -> dict[str, float]:
    child = period_by_coset_index(p, n)
    k = (p - 1) // (2 * n)
    angles = []
    for j in range((p - 1) // (2 * n)):
        a = child[j].real
        b = child[j + k].real
        if a == 0.0 and b == 0.0:
            continue
        theta = math.atan2(b, a)
        if theta < 0:
            theta += 2 * math.pi
        angles.append(theta)
    m = len(angles)
    coeffs = {}
    for ell in range(1, 9):
        c = sum(math.cos(ell * theta) for theta in angles) / m
        s = sum(math.sin(ell * theta) for theta in angles) / m
        coeffs[f"f{ell}"] = math.hypot(c, s)
    counts = [0 for _ in range(bins)]
    for theta in angles:
        counts[min(bins - 1, int(theta * bins / (2 * math.pi)))] += 1
    disc = max(abs(count / m - 1 / bins) for count in counts)
    return {
        "m": float(m),
        "disc": disc,
        "max_f1_8": max(coeffs.values()),
        **coeffs,
    }


def main() -> None:
    cases = []
    for n in (16, 32, 64, 128):
        p = first_prime_congruent_one(2 * n, max((2 * n) ** 4, 100_000))
        if p < 300_000_000:
            cases.append((p, n))
    print("p          n->2n   pairs  disc16   maxF1-8  f1      f2      f3      f4")
    print("-" * 92)
    for p, n in cases:
        st = angle_stats(p, n)
        print(
            f"{p:<10d} {n:<3d}->{2*n:<3d} {int(st['m']):<6d} "
            f"{st['disc']:<8.5f} {st['max_f1_8']:<8.5f} "
            f"{st['f1']:<7.5f} {st['f2']:<7.5f} {st['f3']:<7.5f} {st['f4']:<7.5f}"
        )


if __name__ == "__main__":
    main()
