#!/usr/bin/env python3
"""#466 R256: mass-transport balances behind the trim-five q60 cap.

R255 suggests the residual distribution is lower-bulk/zero-heavy relative to
Exp(1), with the mean restored by the upper tail.  This probe looks for a
simple transport inequality around q60 or around the target 0.75 threshold.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def hinge_stats(values: np.ndarray, center: float) -> tuple[float, float, float, float]:
    above = np.maximum(values - center, 0.0)
    below = np.maximum(center - values, 0.0)
    return (
        float(np.mean(above)),
        float(np.mean(below)),
        float(np.count_nonzero(values >= center) / len(values)),
        float(np.mean(values)),
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
    parser.add_argument("--target-q", type=float, default=0.79049)
    parser.add_argument("--theta", type=float, default=0.75)
    parser.add_argument("--top", type=int, default=16)
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
        q60 = float(np.quantile(residual, 0.6))
        s075 = int(np.count_nonzero(residual >= args.theta)) / case.m
        micro = s075 * math.exp(0.755 / 2.0)
        above_q, below_q, surv_q, mean = hinge_stats(residual, q60)
        above_t, below_t, surv_t, _ = hinge_stats(residual, args.theta)
        above_target, below_target, surv_target, _ = hinge_stats(residual, args.target_q)
        rows.append(
            (
                micro,
                q60,
                mean,
                above_q,
                below_q,
                above_q / below_q if below_q else float("inf"),
                above_t,
                below_t,
                above_t / below_t if below_t else float("inf"),
                above_target,
                below_target,
                surv_target,
                case.n,
                case.p,
                case.m,
            )
        )

    rows.sort(reverse=True)
    print(f"R256 quantile mass transport cases={len(rows)} trim={args.trim}")
    print("micro    q60      mean     Aq60     Bq60     Aq/Bq    A075     B075     A/B075   S@Q*    n     p          M")
    print("-" * 132)
    for row in rows[: args.top]:
        (
            micro,
            q60,
            mean,
            aq,
            bq,
            rq,
            at,
            bt,
            rt,
            _aT,
            _bT,
            sT,
            n,
            p,
            m,
        ) = row
        print(
            f"{micro:<8.6f} {q60:<8.6f} {mean:<8.5f} {aq:<8.5f} {bq:<8.5f} "
            f"{rq:<8.4f} {at:<8.5f} {bt:<8.5f} {rt:<8.4f} {sT:<8.6f} "
            f"{n:<5d} {p:<10d} {m}"
        )

    names = [
        "q60",
        "mean",
        "Aq60",
        "Bq60",
        "Aq/Bq",
        "A075",
        "B075",
        "A/B075",
        "A@Q*",
        "B@Q*",
        "S@Q*",
        "M/n",
        "logM",
    ]
    matrix = []
    target = []
    for row in rows:
        target.append(row[0])
        m = row[-1]
        n = row[-3]
        matrix.append([row[1], row[2], *row[3:12], m / n, math.log(m)])
    matrix_np = np.array(matrix, dtype=float)
    target_np = np.array(target, dtype=float)
    print("\ncorrelations with micro")
    scored = []
    for idx, name in enumerate(names):
        corr = float(np.corrcoef(target_np, matrix_np[:, idx])[0, 1])
        scored.append((abs(corr), name, corr))
    for _abs, name, corr in sorted(scored, reverse=True):
        print(f"{name:<8s} {corr:+.6f}")

    print("\nmax transport ratios")
    for idx, name in [(5, "Aq/Bq"), (8, "A/B075")]:
        row = max(rows, key=lambda r: r[idx])
        print(
            f"{name}={row[idx]:.8f} micro={row[0]:.8f} q60={row[1]:.8f} "
            f"n={row[-3]} p={row[-2]} M={row[-1]}"
        )


if __name__ == "__main__":
    main()
