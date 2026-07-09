#!/usr/bin/env python3
"""#466 R176: near-zero/high-tail compensation in dyadic spectra.

R175 found dyadic spectra have extra near-zero mass and heavier tails compared
with random phase controls, while the R168 MGF barely increases.  This probe
quantifies the compensation by bins.
"""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    subgroup,
)

random.seed(466176)


BINS = [(0.0, 0.25), (0.25, 0.5), (0.5, 1.0), (1.0, 2.0), (2.0, 4.0), (4.0, 8.0), (8.0, float("inf"))]


def dyadic_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def random_phase_values(n: int, samples: int) -> list[float]:
    vals = []
    for _ in range(samples):
        sr = 0.0
        si = 0.0
        for _ in range(n):
            a = random.random() * 2.0 * math.pi
            sr += math.cos(a)
            si += math.sin(a)
        vals.append((sr * sr + si * si) / n)
    mean = sum(vals) / len(vals)
    return [x / mean for x in vals]


def bin_stats(xs: list[float]) -> list[tuple[str, float, float, float]]:
    total_mgf = sum(math.exp(x / 8) for x in xs)
    total_mean = sum(xs)
    out = []
    for lo, hi in BINS:
        vals = [x for x in xs if lo <= x < hi]
        label = f"[{lo:g},{hi:g})" if math.isfinite(hi) else f">={lo:g}"
        frac = len(vals) / len(xs)
        mean_share = sum(vals) / total_mean if total_mean else 0.0
        mgf_share = sum(math.exp(x / 8) for x in vals) / total_mgf if total_mgf else 0.0
        out.append((label, frac, mean_share, mgf_share))
    return out


def summarize(label: str, xs: list[float]) -> None:
    low = sum(1 for x in xs if x < 0.5) / len(xs)
    high = sum(1 for x in xs if x >= 4.0) / len(xs)
    mgf = sum(math.exp(x / 8) for x in xs) / len(xs)
    mean = sum(xs) / len(xs)
    print(f"{label}: mean={mean:.6f} low<0.5={low:.4f} high>=4={high:.4f} mgf={mgf:.6f}")
    print("  " + " ".join(f"{name}:f={frac:.3f},m={mean_share:.3f},e={mgf_share:.3f}"
                            for name, frac, mean_share, mgf_share in bin_stats(xs)))


def main() -> None:
    cases = [(64, 16778497), (128, 268437889), (256, 16777729)]
    for n, p in cases:
        print(f"n={n} p={p}")
        dy = dyadic_values(p, n)
        rp = random_phase_values(n, samples=min(300_000, max(50_000, (p - 1) // n)))
        summarize("dyadic", dy)
        summarize("random", rp)
        print()


if __name__ == "__main__":
    main()
