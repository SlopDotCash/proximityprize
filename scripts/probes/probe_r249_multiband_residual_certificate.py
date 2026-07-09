#!/usr/bin/env python3
"""#466 R249: finite multiband certificates for the trim-five residual CDF.

R248 shows that one bulk cap plus one high-tail cap is too coarse because the
short band [0.75, 0.875) loses too much under raw survival monotonicity.

This probe searches for small threshold grids `bands` such that the following
finite certificate implies the target half-rate CDF:

    S(theta) <= B_i for theta in [t_i, t_{i+1})
    S(theta) <= C_tail exp(-theta/2) for theta >= t_last.

The finite-band implication cost on [t_i, t_{i+1}) is

    B_i * exp(t_{i+1}/2)

so each band must stay below target C=0.6012.
"""

from __future__ import annotations

import argparse
import itertools
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def survival(residual: np.ndarray, theta: float, m: int) -> float:
    return int(np.count_nonzero(residual >= theta)) / m


def tail_constant(residual: np.ndarray, cutoff: float, m: int) -> tuple[float, float, int]:
    best = (0.0, cutoff, 0)
    for idx, x0 in enumerate(residual, start=1):
        theta = float(x0)
        if theta < cutoff:
            break
        c = (idx / m) * math.exp(theta / 2.0)
        if c > best[0]:
            best = (c, theta, idx)
    return best


def precompute_thresholds(cases, trim: int, thresholds: list[float]) -> dict[float, tuple]:
    out = {}
    for threshold in thresholds:
        best_bulk = (0.0, 0, 0, 0)
        best_tail = (0.0, threshold, 0, 0, 0, 0)
        for case in cases:
            residual = case.desc[min(trim, len(case.desc)) :]
            s = survival(residual, threshold, case.m)
            bulk_row = (s, case.n, case.p, case.m)
            if bulk_row > best_bulk:
                best_bulk = bulk_row
            c, theta, count = tail_constant(residual, threshold, case.m)
            tail_row = (c, theta, count, case.n, case.p, case.m)
            if tail_row > best_tail:
                best_tail = tail_row
        out[threshold] = (best_bulk, best_tail)
    return out


def evaluate_grid(precomputed: dict[float, tuple], bands: tuple[float, ...]) -> tuple[float, list[tuple]]:
    rows = []
    worst_cost = 0.0
    for i, theta in enumerate(bands[:-1]):
        next_theta = bands[i + 1]
        best, _tail = precomputed[theta]
        cost = best[0] * math.exp(next_theta / 2.0)
        rows.append(("band", theta, next_theta, cost, best[0], 0.0, 0, *best[1:]))
        worst_cost = max(worst_cost, cost)

    cutoff = bands[-1]
    _bulk, best_tail = precomputed[cutoff]
    rows.append(("tail", cutoff, float("inf"), best_tail[0], 0.0, best_tail[1], best_tail[2], best_tail[3], best_tail[4], best_tail[5]))
    worst_cost = max(worst_cost, best_tail[0])
    return worst_cost, rows


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
    parser.add_argument("--target-c", type=float, default=0.6012)
    parser.add_argument("--start", type=float, default=0.75)
    parser.add_argument(
        "--candidates",
        type=float,
        nargs="+",
        default=[0.775, 0.8, 0.825, 0.85, 0.875, 0.9, 0.95, 1.0, 1.125],
    )
    parser.add_argument("--max-extra", type=int, default=4)
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

    candidates = sorted(x for x in args.candidates if x > args.start)
    precomputed = precompute_thresholds(cases, args.trim, [args.start, *candidates])
    scans = []
    for k in range(1, args.max_extra + 1):
        for extra in itertools.combinations(candidates, k):
            bands = (args.start, *extra)
            cost, rows = evaluate_grid(precomputed, bands)
            scans.append((cost, bands, rows))
    scans.sort(key=lambda row: (row[0], len(row[1]), row[1]))

    print(
        f"R249 multiband residual certificate cases={len(cases)} trim={args.trim} "
        f"target_C={args.target_c}"
    )
    print("best grids")
    print("cost     slack    bands")
    print("-" * 96)
    for cost, bands, _rows in scans[: args.top]:
        print(f"{cost:<8.6f} {args.target_c-cost:<8.6f} {bands}")

    if scans:
        cost, bands, rows = scans[0]
        print("\nbest grid details")
        print(f"bands={bands} cost={cost:.8f} slack={args.target_c-cost:.8f}")
        print("kind  theta    next     cost     S_cap    tailTheta count  n     p          M")
        print("-" * 104)
        for kind, theta, next_theta, row_cost, s_cap, tail_theta, count, n, p, m in rows:
            next_text = "inf" if math.isinf(next_theta) else f"{next_theta:.3f}"
            print(
                f"{kind:<5s} {theta:<8.3f} {next_text:<8s} {row_cost:<8.6f} "
                f"{s_cap:<8.6f} {tail_theta:<9.6f} {count:<6d} {n:<5d} {p:<10d} {m}"
            )


if __name__ == "__main__":
    main()
