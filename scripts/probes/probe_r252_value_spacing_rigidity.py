#!/usr/bin/env python3
"""#466 R252: value-spacing rigidity near the R251 micro-band.

R251 leaves a very tight main-lane micro-band cap:

    S(0.75) * exp(0.755/2) <= 0.6012.

R244 showed the threshold set is Fourier-uniform in quotient-index space, so
this probe instead studies the value-space geometry around the cutoff.  It
asks whether the near-worst rows have a forced gap, local density constraint,
or order-statistic slope near the 0.75 boundary.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def local_stats(desc: np.ndarray, m: int, trim: int, theta: float, cutoff: float) -> tuple:
    residual = desc[min(trim, len(desc)) :]
    count_theta = int(np.count_nonzero(residual >= theta))
    count_cutoff = int(np.count_nonzero(residual >= cutoff))
    micro = (count_theta / m) * math.exp(cutoff / 2.0)
    edge_hi = float(residual[count_theta - 1]) if count_theta else 0.0
    edge_lo = float(residual[count_theta]) if count_theta < len(residual) else 0.0
    cut_hi = float(residual[count_cutoff - 1]) if count_cutoff else 0.0
    cut_lo = float(residual[count_cutoff]) if count_cutoff < len(residual) else 0.0
    # Local density in short value windows above theta.
    windows = []
    for width in [0.005, 0.01, 0.02, 0.05, 0.1]:
        c = int(np.count_nonzero((residual >= theta) & (residual < theta + width)))
        windows.append(c / m)
    # Slope of the order statistic curve around the boundary.
    slopes = []
    for radius in [4, 8, 16, 32]:
        lo = max(0, count_theta - radius)
        hi = min(len(residual) - 1, count_theta + radius)
        if hi > lo:
            slopes.append((float(residual[lo]) - float(residual[hi])) / ((hi - lo) / m))
        else:
            slopes.append(0.0)
    return (
        micro,
        count_theta / m,
        count_cutoff / m,
        count_theta,
        count_cutoff,
        edge_hi,
        edge_lo,
        edge_hi - edge_lo,
        cut_hi,
        cut_lo,
        cut_hi - cut_lo,
        *windows,
        *slopes,
    )


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
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--cutoff", type=float, default=0.755)
    parser.add_argument("--top", type=int, default=20)
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
        stats = local_stats(case.desc, case.m, args.trim, args.theta, args.cutoff)
        rows.append((*stats, case.n, case.p, case.m))
    rows.sort(reverse=True)

    print(
        f"R252 value-spacing rigidity cases={len(rows)} trim={args.trim} "
        f"theta={args.theta} cutoff={args.cutoff}"
    )
    print("micro    S075     S755     c075  c755  edgeGap  cutGap   w005    w010    w020    n     p          M")
    print("-" * 126)
    for row in rows[: args.top]:
        (
            micro,
            s075,
            s755,
            c075,
            c755,
            _edge_hi,
            _edge_lo,
            edge_gap,
            _cut_hi,
            _cut_lo,
            cut_gap,
            w005,
            w010,
            w020,
            _w050,
            _w100,
            *_slopes_and_id,
        ) = row
        n, p, m = row[-3:]
        print(
            f"{micro:<8.6f} {s075:<8.6f} {s755:<8.6f} {c075:<5d} {c755:<5d} "
            f"{edge_gap:<8.6f} {cut_gap:<8.6f} {w005:<8.6f} {w010:<8.6f} "
            f"{w020:<8.6f} {n:<5d} {p:<10d} {m}"
        )

    names = ["S075", "S755", "edgeGap", "cutGap", "w005", "w010", "w020", "w050", "w100", "slope4", "slope8", "slope16", "slope32", "M/n", "logM"]
    matrix = []
    target = []
    for row in rows:
        target.append(row[0])
        m = row[-1]
        n = row[-3]
        matrix.append([
            row[1],
            row[2],
            row[7],
            row[10],
            row[11],
            row[12],
            row[13],
            row[14],
            row[15],
            row[16],
            row[17],
            row[18],
            row[19],
            m / n,
            math.log(m),
        ])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)
    print("\ncorrelations with micro")
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])
        print(f"{name:<8s} {corr:+.6f}")


if __name__ == "__main__":
    main()
