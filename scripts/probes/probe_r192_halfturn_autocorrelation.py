#!/usr/bin/env python3
"""#466 R192: half-turn autocorrelation anatomy of the R191 product MGF.

For child level μ_n, write

  f_j = exp(X_j / 8),  X_j = |eta_j|^2 / mean(|eta|^2).

The dyadic product budget for the parent μ_{2n} is the half-turn
autocorrelation

  (2/M) * sum_{0 <= j < M/2} f_j f_{j+M/2},

where M=(p-1)/n.  If f is close to a real-Gaussian chi-square observable and
the half-turn correlation is negligible, this should be close to
(E f)^2 = (sqrt(4/3))^2 = 4/3.

This probe decomposes the product budget into mean^2 plus centered half-turn
covariance and reports the dominant Fourier modes of the centered sequence.
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def normalized(vals: list[complex]) -> list[float]:
    sigma = sum(abs(z) ** 2 for z in vals) / len(vals)
    return [abs(z) ** 2 / sigma for z in vals]


def dft_power_top(centered: list[float], top_k: int = 6) -> list[tuple[int, float]]:
    m = len(centered)
    total_power = sum(x * x for x in centered)
    rows: list[tuple[int, float]] = []
    # Direct DFT is fine for these moderate quotient lengths.
    for ell in range(1, min(m, 256)):
        z = 0j
        for j, x in enumerate(centered):
            z += x * cmath.exp(-2j * math.pi * ell * j / m)
        # Parseval normalization: sum |hat|^2 / M = sum x^2.
        frac = (abs(z) ** 2 / m) / total_power if total_power else 0.0
        rows.append((ell, frac))
    return sorted(rows, key=lambda row: row[1], reverse=True)[:top_k]


def stats(p: int, n: int) -> dict[str, object]:
    vals = period_by_coset_index(p, n)
    x = normalized(vals)
    f = [math.exp(xx / 8) for xx in x]
    m = len(f)
    half = m // 2
    mean = sum(f) / m
    product = sum(f[j] * f[j + half] for j in range(half)) / half
    centered = [v - mean for v in f]
    cov = sum(centered[j] * centered[j + half] for j in range(half)) / half
    var = sum(c * c for c in centered) / m
    corr = cov / var if var else 0.0
    odd_energy = sum((centered[j] - centered[j + half]) ** 2 for j in range(half)) / (2 * m)
    even_energy = sum((centered[j] + centered[j + half]) ** 2 for j in range(half)) / (2 * m)
    return {
        "m": m,
        "mean": mean,
        "mean_sq": mean * mean,
        "product": product,
        "cov": cov,
        "var": var,
        "corr": corr,
        "even_energy": even_energy,
        "odd_energy": odd_energy,
        "top": dft_power_top(centered),
    }


def main() -> None:
    cases = [
        (16, 1048609),
        (32, 16778497),
        (64, 16778497),
        (128, 268437889),
        (256, 16777729),
    ]
    print("n p M mean mean^2 product cov corr evenE oddE topFourier(ell:frac)")
    for n, p in cases:
        st = stats(p, n)
        top = ",".join(f"{ell}:{frac:.3f}" for ell, frac in st["top"])
        print(
            f"{n:<3d} {p:<10d} {st['m']:<8d} "
            f"{st['mean']:.6f} {st['mean_sq']:.6f} {st['product']:.6f} "
            f"{st['cov']:+.6e} {st['corr']:+.4f} "
            f"{st['even_energy']:.6e} {st['odd_energy']:.6e} {top}"
        )


if __name__ == "__main__":
    main()
