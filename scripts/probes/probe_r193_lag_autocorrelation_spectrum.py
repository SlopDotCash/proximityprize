#!/usr/bin/env python3
"""#466 R193: lag-autocorrelation spectrum for the product-MGF observable.

R192 found that the dyadic half-turn covariance of

  f_j = exp((|eta_j|^2 / sigma^2) / 8)

is tiny.  This probe checks whether that is a special half-turn cancellation or
part of a broader small-autocorrelation law on the quotient coset cycle.

For selected lags h, it reports

  cov_h = avg_j (f_j-mean) (f_{j+h}-mean),  corr_h = cov_h / var(f).

The dyadic parent product budget uses h = M/2.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def normalized(vals: list[complex]) -> list[float]:
    sigma = sum(abs(z) ** 2 for z in vals) / len(vals)
    return [abs(z) ** 2 / sigma for z in vals]


def lag_profile(p: int, n: int) -> dict[str, object]:
    vals = period_by_coset_index(p, n)
    x = normalized(vals)
    f = [math.exp(xx / 8) for xx in x]
    m = len(f)
    mean = sum(f) / m
    centered = [v - mean for v in f]
    var = sum(v * v for v in centered) / m
    base_lags = [1, 2, 3, 4, 5, 8, 13, 21, 34, m // 8, m // 4, 3 * m // 8, m // 2]
    lags = sorted({h % m for h in base_lags if h % m != 0})
    rows = []
    for h in lags:
        cov = sum(centered[j] * centered[(j + h) % m] for j in range(m)) / m
        rows.append((h, cov, cov / var if var else 0.0))
    max_abs = max(rows, key=lambda r: abs(r[2]))
    half = next(r for r in rows if r[0] == m // 2)
    return {
        "m": m,
        "mean": mean,
        "var": var,
        "rows": rows,
        "max_abs": max_abs,
        "half": half,
    }


def main() -> None:
    cases = [
        (16, 1048609),
        (32, 16778497),
        (64, 16778497),
        (128, 268437889),
        (256, 16777729),
    ]
    print("n p M mean var halfCorr maxAbsCorr@lag selected_lags(corr)")
    for n, p in cases:
        st = lag_profile(p, n)
        selected = " ".join(f"{h}:{corr:+.4f}" for h, _cov, corr in st["rows"])
        hmax, _cmax, corrmax = st["max_abs"]
        _hhalf, _chalf, corrhalf = st["half"]
        print(
            f"{n:<3d} {p:<10d} {st['m']:<8d} {st['mean']:.6f} {st['var']:.6e} "
            f"{corrhalf:+.4f} {corrmax:+.4f}@{hmax} {selected}"
        )


if __name__ == "__main__":
    main()
