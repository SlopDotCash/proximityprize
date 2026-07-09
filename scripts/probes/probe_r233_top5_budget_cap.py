#!/usr/bin/env python3
"""#466 R233: top-five MGF budget cap diagnostics.

R231 found a promising certificate:

    trim = 5, tau = 0.75, K = 0, C ~= 0.6012.

This probe separates the top-five exact staircase/MGF contribution from the
residual envelope.  It asks what kind of uniform top-order-statistic bound would
be needed to make the R231 certificate theorem-shaped.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r217_normalized_sq_grid_budget import staircase_deltas  # noqa: E402
from scripts.probes.probe_r231_top_spike_trimmed_mgf import medium_cases  # noqa: E402


def top_exact_mgf(desc: np.ndarray, trim: int, rate: float) -> float:
    top = desc[: min(trim, len(desc))]
    return float(np.exp(rate * top).sum() / len(desc))


def top_stair_budget(desc: np.ndarray, trim: int, step: float, cutoff: float, rate: float) -> float:
    top = desc[: min(trim, len(desc))]
    if len(top) == 0:
        return 0.0
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        total += delta * int(np.count_nonzero(top >= theta))
    return total / len(desc)


def residual_envelope_budget(
    carrier: int, step: float, cutoff: float, rate: float, tau: float, c_bulk: float
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        bound = 1.0 if theta <= tau + 1e-15 else c_bulk * math.exp(-theta / 2.0)
        total += delta * bound
    return total


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
    parser.add_argument("--tau", type=float, default=0.75)
    parser.add_argument("--c-bulk", type=float, default=0.60110935)
    parser.add_argument("--step", type=float, default=0.03125)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--cutoff", type=float, default=0.0)
    parser.add_argument("--top", type=int, default=30)
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
        cutoff = max(args.cutoff, float(case.desc[0]))
        top_mgf = top_exact_mgf(case.desc, args.trim, args.rate)
        top_stair = top_stair_budget(case.desc, args.trim, args.step, cutoff, args.rate)
        resid = residual_envelope_budget(case.m, args.step, cutoff, args.rate, args.tau, args.c_bulk)
        total = top_stair + resid
        max_x = float(case.desc[0])
        fifth = float(case.desc[min(args.trim - 1, len(case.desc) - 1)])
        rows.append((total, top_stair, top_mgf, resid, max_x, fifth, case.m, case.n, case.p, case.label))

    rows.sort(reverse=True)
    print(
        "R233 top-five budget cap diagnostics "
        f"cases={len(rows)} trim={args.trim} tau={args.tau} C={args.c_bulk} step={args.step}"
    )
    print("total    slack    topStair topMGF   resid    maxX     fifth    M      n     p          label")
    print("-" * 120)
    for total, top_stair, top_mgf, resid, max_x, fifth, m, n, p, label in rows[: args.top]:
        print(
            f"{total:<8.4f} {2-total:<8.4f} {top_stair:<8.4f} {top_mgf:<8.4f} "
            f"{resid:<8.4f} {max_x:<8.3f} {fifth:<8.3f} {m:<6d} {n:<5d} {p:<10d} {label}"
        )

    print("\nsummary")
    if rows:
        worst = rows[0]
        worst_top = max(rows, key=lambda r: r[1])
        worst_max = max(rows, key=lambda r: r[4])
        print(f"worst_total={worst[0]:.6f} slack={2-worst[0]:.6f} n={worst[7]} p={worst[8]} M={worst[6]}")
        print(
            f"worst_top_stair={worst_top[1]:.6f} topMGF={worst_top[2]:.6f} "
            f"n={worst_top[7]} p={worst_top[8]} M={worst_top[6]}"
        )
        print(f"worst_maxX={worst_max[4]:.6f} fifth={worst_max[5]:.6f} n={worst_max[7]} p={worst_max[8]} M={worst_max[6]}")
        print(f"max_top_stair_per_logM={max(r[1] / math.log(max(r[6], 2)) for r in rows):.6f}")


if __name__ == "__main__":
    main()
