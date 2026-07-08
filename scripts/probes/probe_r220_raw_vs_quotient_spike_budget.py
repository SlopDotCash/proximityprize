#!/usr/bin/env python3
"""#466 R220: compare quotient-coset and raw-frequency spike budgets.

R219's formal carrier is the raw nonzero frequency set.  Exact vectorized
probes usually evaluate one representative per μ_n-coset because |η_b| is
coset-constant.  A quotient tail

    N_q(T) <= C * M * exp(-T/2) + K

with M = (p-1)/n translates to the raw-frequency tail

    N_raw(T) = n * N_q(T)
             <= C * (p-1) * exp(-T/2) + n*K.

This probe computes the same exact coset spectrum and reports both excesses.
It distinguishes a real tail failure from the expected multiplicity scaling of
the additive spike budget.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    normalized_values_vectorized,
)


DEFAULT_ROWS: tuple[tuple[int, int, str], ...] = (
    (32, 32801, "r202-worst-large-spike"),
    (32, 1153, "r200-worst-spike-ratio"),
    (64, 7937, "r202-medium-mgf-counterexample"),
    (128, 268438913, "large-anchor"),
    (256, 16780289, "large-grid-start"),
)


def tail_excess(xs, c_bulk: float, spike_budget: float, step: float) -> tuple[float, float, int]:
    max_x = float(xs.max())
    worst_excess = -1.0e100
    worst_theta = 0.0
    worst_count = 0
    j = 2
    while j * step <= max_x + 1.0e-12:
        theta = j * step
        count = int((xs >= theta).sum())
        bound = c_bulk * len(xs) * math.exp(-theta / 2) + spike_budget
        excess = count - bound
        if excess > worst_excess:
            worst_excess = excess
            worst_theta = theta
            worst_count = count
        j += 1
    return worst_excess, worst_theta, worst_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--skip-large", action="store_true")
    args = parser.parse_args()

    rows = []
    for n, p, label in DEFAULT_ROWS:
        if args.skip_large and p > 20_000_000:
            continue
        xs = normalized_values_vectorized(p, n, args.chunk)
        q_excess, q_theta, q_count = tail_excess(xs, args.c_bulk, args.spike_budget, args.step)
        raw_literal_excess = n * q_count - (
            args.c_bulk * (p - 1) * math.exp(-q_theta / 2) + args.spike_budget
        )
        raw_scaled_excess = n * q_count - (
            args.c_bulk * (p - 1) * math.exp(-q_theta / 2) + n * args.spike_budget
        )
        rows.append(
            (
                raw_literal_excess,
                raw_scaled_excess,
                q_excess,
                q_theta,
                q_count,
                float((xs >= q_theta).sum()) * n,
                float(xs.max()),
                float(np.exp(xs / 4).mean()),
                len(xs),
                n,
                p,
                label,
            )
        )

    rows.sort(reverse=True)
    print(
        f"R220 raw-vs-quotient spike budget C={args.c_bulk} K={args.spike_budget} "
        f"step={args.step} rows={len(rows)}"
    )
    print("rawLitEx  rawScaleEx qExcess   T,count_q raw_count maxX    mgf1/4  M       n    p          label")
    print("-" * 130)
    for raw_lit, raw_scaled, q_ex, theta, q_count, raw_count, max_x, mgf4, m, n, p, label in rows:
        print(
            f"{raw_lit:>9.3f} {raw_scaled:>10.3f} {q_ex:>8.3f} "
            f"{theta:<4.1f},{q_count:<7d} {int(raw_count):<9d} "
            f"{max_x:<7.3f} {mgf4:<7.4f} {m:<7d} {n:<4d} {p:<10d} {label}"
        )

    print("\nsummary")
    print(f"max_raw_literal_excess={max(r[0] for r in rows):.6f}")
    print(f"max_raw_scaled_excess={max(r[1] for r in rows):.6f}")
    print(f"max_quotient_excess={max(r[2] for r in rows):.6f}")


if __name__ == "__main__":
    main()
