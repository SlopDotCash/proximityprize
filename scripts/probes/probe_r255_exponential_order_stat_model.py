#!/usr/bin/env python3
"""#466 R255: exponential order-statistic model for the trim-five q60 cap.

For a complex Gaussian Gauss-period model, normalized squared magnitudes should
look roughly Exp(1).  R253's q60 maximum ~0.79049 is above the Exp(1) q60
(-log 0.4 ~= 0.916 for ascending q60? depending on convention), so this probe
carefully compares the residual descending/ascending conventions and finite
trim effects against exponential order statistics.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def exp_survival_quantile(survival: float) -> float:
    return -math.log(survival)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=8)
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--cache-dir", type=Path, default=Path(".cache/proximity-r231"))
    parser.add_argument("--cache-only", action="store_true")
    parser.add_argument("--trim", type=int, default=5)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.medium_max_index,
        args.min_index,
        args.chunk,
        args.cache_dir,
        args.cache_only,
    )

    rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        # np.quantile on descending data is numerically the same multiset
        # quantile: q=0.6 means 60% of values are <= q60, so survival is 0.4.
        q60 = float(np.quantile(residual, 0.6))
        q55 = float(np.quantile(residual, 0.55))
        q65 = float(np.quantile(residual, 0.65))
        s075 = int(np.count_nonzero(residual >= 0.75)) / case.m
        micro = s075 * math.exp(0.755 / 2.0)
        mean = float(np.mean(residual))
        exp_q60 = exp_survival_quantile(0.4)
        centered_q60 = q60 / mean if mean else 0.0
        rows.append((micro, q60, q60 - exp_q60, centered_q60, mean, q55, q65, s075, case.n, case.p, case.m))

    rows.sort(reverse=True)
    exp_q60 = exp_survival_quantile(0.4)
    print(f"R255 exponential order-stat model cases={len(rows)} trim={args.trim}")
    print(f"Exp(1) ascending q60 = -log(0.4) = {exp_q60:.9f}")
    print("micro    q60      q60-exp  q60/mean mean     q55      q65      S075     n     p          M")
    print("-" * 116)
    for row in rows[: args.top]:
        micro, q60, gap, centered, mean, q55, q65, s075, n, p, m = row
        print(
            f"{micro:<8.6f} {q60:<8.6f} {gap:<8.6f} {centered:<8.5f} {mean:<8.5f} "
            f"{q55:<8.6f} {q65:<8.6f} {s075:<8.6f} {n:<5d} {p:<10d} {m}"
        )

    vals = np.array([[r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]] for r in rows])
    print("\nsummary")
    labels = ["micro", "q60", "q60-exp", "q60/mean", "mean", "q55", "q65", "S075"]
    for idx, label in enumerate(labels):
        col = vals[:, idx]
        print(
            f"{label:<9s} min={float(np.min(col)):.6f} median={float(np.median(col)):.6f} "
            f"p95={float(np.quantile(col,0.95)):.6f} max={float(np.max(col)):.6f}"
        )


if __name__ == "__main__":
    main()
