#!/usr/bin/env python3
"""#466 R242: anatomy of the trim-five first-band obstruction.

R238-R241 reduce the live residual theorem to the first band near theta=0.75.
This probe prints enough per-row anatomy to decide whether the obstruction is
visible in coarse distribution shape, early order statistics, or index-level
arithmetic.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def row_stats(case, trim: int, theta: float) -> tuple:
    residual = case.desc[min(trim, len(case.desc)) :]
    count = int(np.count_nonzero(residual >= theta))
    frac = count / case.m
    half_c = frac * math.exp(theta / 2.0)
    mean = float(residual.mean())
    second = float(np.mean(residual * residual))
    var = second - mean * mean
    q50, q60, q70, q80, q90 = [float(np.quantile(residual, q)) for q in [0.5, 0.6, 0.7, 0.8, 0.9]]
    top = [float(x) for x in residual[:8]]
    boundary = float(residual[count - 1]) if count else 0.0
    next_val = float(residual[count]) if count < len(residual) else 0.0
    return (
        half_c,
        frac,
        count,
        mean,
        second,
        var,
        q50,
        q60,
        q70,
        q80,
        q90,
        boundary,
        next_val,
        top,
        case.m / case.n,
        case.m,
        case.n,
        case.p,
        case.label,
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

    rows = [row_stats(case, args.trim, args.theta) for case in cases]
    rows.sort(reverse=True)

    print(
        f"R242 residual first-band anatomy cases={len(rows)} trim={args.trim} "
        f"theta={args.theta}"
    )
    print(
        "half_C   frac     mean     var      q50      q70      q90      "
        "edge>=   edge<    M/n      M      n     p"
    )
    print("-" * 118)
    for row in rows[: args.top]:
        half_c, frac, count, mean, _second, var, q50, _q60, q70, _q80, q90, boundary, next_val, _top, mn, m, n, p, _label = row
        print(
            f"{half_c:<8.6f} {frac:<8.6f} {mean:<8.5f} {var:<8.5f} "
            f"{q50:<8.5f} {q70:<8.5f} {q90:<8.5f} {boundary:<8.5f} "
            f"{next_val:<8.5f} {mn:<8.4f} {m:<6d} {n:<5d} {p}"
        )

    print("\nworst row residual top order stats")
    if rows:
        worst = rows[0]
        print(f"n={worst[16]} p={worst[17]} M={worst[15]} M/n={worst[14]:.6f}")
        print(" ".join(f"{x:.6f}" for x in worst[13]))

    print("\ncorrelations with half_C")
    names = [
        "frac",
        "mean",
        "second",
        "var",
        "q50",
        "q60",
        "q70",
        "q80",
        "q90",
        "M/n",
        "logM",
    ]
    matrix = np.array(
        [
            [
                row[1],
                row[3],
                row[4],
                row[5],
                row[6],
                row[7],
                row[8],
                row[9],
                row[10],
                row[14],
                math.log(row[15]),
            ]
            for row in rows
        ],
        dtype=float,
    )
    target = np.array([row[0] for row in rows], dtype=float)
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(target, matrix[:, idx])[0, 1])
        print(f"{name:<8s} {corr:+.6f}")

    print("\nquantile maxima over all cached cases")
    for q, idx in [("q50", 6), ("q60", 7), ("q70", 8), ("q80", 9), ("q90", 10)]:
        row = max(rows, key=lambda r: r[idx])
        print(f"{q}={row[idx]:.8f} half_C={row[0]:.8f} n={row[16]} p={row[17]} M={row[15]}")


if __name__ == "__main__":
    main()
