#!/usr/bin/env python3
"""#466 R253: global quantile envelopes for trim-five residual spectra.

R252 refutes local value-spacing rigidity.  R253 asks whether the residual
micro-band cap is part of a global quantile envelope that might be attacked by
majorization or stochastic domination.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


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
    parser.add_argument("--top", type=int, default=10)
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

    ps = [0.50, 0.525, 0.55, 0.575, 0.60, 0.625, 0.65, 0.70, 0.75, 0.80, 0.90]
    rows_by_p = {p: [] for p in ps}
    shape_rows = []
    for case in cases:
        residual = case.desc[min(args.trim, len(case.desc)) :]
        qs = {p: float(np.quantile(residual, p)) for p in ps}
        for p, q in qs.items():
            rows_by_p[p].append((q, case.n, case.p, case.m))
        # Ratios try to detect a universal one-parameter shape.
        q60 = qs[0.60]
        q50 = qs[0.50]
        q70 = qs[0.70]
        s075 = int(np.count_nonzero(residual >= 0.75)) / case.m
        micro = s075 * math.exp(0.755 / 2.0)
        shape_rows.append((micro, q60, q60 / q50 if q50 else 0.0, q70 / q60 if q60 else 0.0, q70 - q50, case.n, case.p, case.m))

    print(f"R253 quantile envelope fit cases={len(cases)} trim={args.trim}")
    print("\nquantile maxima")
    print("p       maxQ      p95Q      medianQ   arg(n,p,M)")
    print("-" * 78)
    for p in ps:
        vals = sorted(rows_by_p[p], reverse=True)
        only = [row[0] for row in vals]
        best = vals[0]
        print(
            f"{p:<7.3f} {best[0]:<9.6f} {float(np.quantile(only,0.95)):<9.6f} "
            f"{float(np.median(only)):<9.6f} {best[1]},{best[2]},{best[3]}"
        )

    shape_rows.sort(reverse=True)
    print("\nworst micro rows with quantile shape")
    print("micro    q60      q60/q50  q70/q60  q70-q50  n     p          M")
    print("-" * 92)
    for row in shape_rows[: args.top]:
        micro, q60, r6050, r7060, d7050, n, p, m = row
        print(
            f"{micro:<8.6f} {q60:<8.6f} {r6050:<8.5f} {r7060:<8.5f} "
            f"{d7050:<8.5f} {n:<5d} {p:<10d} {m}"
        )

    names = ["q60", "q60/q50", "q70/q60", "q70-q50", "M/n", "logM"]
    matrix = np.array(
        [[row[1], row[2], row[3], row[4], row[7] / row[5], math.log(row[7])] for row in shape_rows],
        dtype=float,
    )
    target = np.array([row[0] for row in shape_rows], dtype=float)
    print("\ncorrelations with micro")
    for idx, name in enumerate(names):
        print(f"{name:<8s} {float(np.corrcoef(target, matrix[:, idx])[0,1]):+.6f}")


if __name__ == "__main__":
    main()
