#!/usr/bin/env python3
"""#466 R246: refined bulk-shape envelopes for the trim-five residual CDF.

R245 leaves a direct vertical-distribution socket.  This probe tests whether a
simple transformed variable has a universal concavity/shape envelope that would
imply the first-band cap.

The main transforms are:

* exponential survival profile: S(theta) * exp(theta / 2)
* log-survival slope between adjacent grid thresholds
* quantile function of the residual spectrum

The probe reports envelope maxima and monotonicity violations across cached
exact spectra.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def survival(residual: np.ndarray, theta: float, m: int) -> float:
    return int(np.count_nonzero(residual >= theta)) / m


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
    parser.add_argument(
        "--thetas",
        type=float,
        nargs="+",
        default=[
            0.50,
            0.625,
            0.75,
            0.875,
            1.0,
            1.125,
            1.25,
            1.5,
            1.75,
            2.0,
            2.5,
            3.0,
        ],
    )
    parser.add_argument(
        "--quantiles",
        type=float,
        nargs="+",
        default=[0.50, 0.55, 0.58, 0.59, 0.60, 0.61, 0.625, 0.65, 0.70],
    )
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

    print(f"R246 bulk shape envelope cases={len(cases)} trim={args.trim}")
    print("\nscaled survival envelope")
    print("theta   max_S    max_halfC  arg(n,p,M)          median_halfC  p95_halfC")
    print("-" * 88)
    half_by_theta: dict[float, list[float]] = {}
    for theta in args.thetas:
        rows = []
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            s = survival(residual, theta, case.m)
            half_c = s * math.exp(theta / 2.0)
            rows.append((half_c, s, case.n, case.p, case.m))
        rows.sort(reverse=True)
        half_by_theta[theta] = [row[0] for row in rows]
        best = rows[0]
        print(
            f"{theta:<7.3f} {best[1]:<8.6f} {best[0]:<10.6f} "
            f"{best[2]},{best[3]},{best[4]:<10d} "
            f"{float(np.median(half_by_theta[theta])):<13.6f} "
            f"{float(np.quantile(half_by_theta[theta], 0.95)):<10.6f}"
        )

    print("\nlog-survival slopes for worst first-band rows")
    first_rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        s075 = survival(residual, 0.75, case.m)
        first_rows.append((s075 * math.exp(0.375), case, residual))
    first_rows.sort(reverse=True, key=lambda row: row[0])
    print("n     p          M      halfC075 slopes")
    print("-" * 92)
    for half_c, case, residual in first_rows[:8]:
        slopes = []
        for a, b in zip(args.thetas, args.thetas[1:]):
            sa = max(survival(residual, a, case.m), 1.0 / case.m)
            sb = max(survival(residual, b, case.m), 1.0 / case.m)
            slopes.append(-math.log(sb / sa) / (b - a))
        print(
            f"{case.n:<5d} {case.p:<10d} {case.m:<6d} {half_c:<9.6f} "
            + " ".join(f"{x:.2f}" for x in slopes[:8])
        )

    print("\nquantile envelope")
    print("q       max_Q     arg(n,p,M)          median_Q   p95_Q")
    print("-" * 78)
    for q in args.quantiles:
        rows = []
        for case in cases:
            residual = case.desc[min(args.trim, len(case.desc)) :]
            val = float(np.quantile(residual, q))
            rows.append((val, case.n, case.p, case.m))
        rows.sort(reverse=True)
        vals = [row[0] for row in rows]
        best = rows[0]
        print(
            f"{q:<7.3f} {best[0]:<9.6f} {best[1]},{best[2]},{best[3]:<10d} "
            f"{float(np.median(vals)):<10.6f} {float(np.quantile(vals, 0.95)):<9.6f}"
        )


if __name__ == "__main__":
    main()
