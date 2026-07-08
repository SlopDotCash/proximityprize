#!/usr/bin/env python3
"""#466 R65: top-coset concentration in dyadic spike examples.

R64 showed bounded super-Wick windows for dyadic μ_{2^a}.  This probe tests
whether those windows are driven by a tiny exceptional tail of Gauss-period
cosets, which would point to a viable counting/tail theorem instead of
moment-ratio monotonicity.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    dfact,
    ratios_from_cosets,
    subgroup,
)


def concentration(p: int, n: int, peak_r: int) -> tuple[float, list[tuple[float, int]], list[tuple[int, float]]]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    xs = sorted((m / sigma2 for m in mags), reverse=True)
    thresholds = [(t, sum(1 for x in xs if x >= t)) for t in (2, 4, 8, 12, 16, 20, 24, 32)]
    weights = [x**peak_r for x in xs]
    total = sum(weights)
    top_shares = [(k, sum(weights[:k]) / total) for k in (1, 2, 4, 8, 16, 32, 64) if k <= len(xs)]
    return xs[0], thresholds, top_shares


def peak_r(p: int, n: int, max_r: int) -> tuple[int, float]:
    rs = ratios_from_cosets(p, n, coset_mags2(p, subgroup(p, n)), max_r)
    return max(enumerate(rs, start=1), key=lambda x: x[1])


def main() -> None:
    cases = [
        (32, 32993, 16),
        (64, 264769, 16),
        (64, 16778497, 20),
        (128, 2101249, 14),
        (64, 16777601, 16),
        (128, 268437889, 12),
    ]
    for n, p, max_r in cases:
        r, rval = peak_r(p, n, max_r)
        xmax, thresholds, shares = concentration(p, n, r)
        print(f"n={n} p={p} peak=R{r}={rval:.6g} xmax/sigma2={xmax:.6g}")
        print("  counts " + " ".join(f">={t:g}:{c}" for t, c in thresholds))
        print("  peak-share " + " ".join(f"top{k}:{s:.4f}" for k, s in shares))
        # Crude one-coset envelope for high r: max^r/(2r-1)!! times coset weight.
        coset_count = (p - 1) // n
        envelope = xmax**r / (dfact(2 * r - 1) * coset_count)
        print(f"  one-coset-envelope-at-peak={envelope:.6g}")


if __name__ == "__main__":
    main()
