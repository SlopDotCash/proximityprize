#!/usr/bin/env python3
"""#466 R262: actual mass on high weighted-tail survivor sets.

R261 refuted a positive weighted fine-tail bound.  This probe measures whether
those same high weighted-tail survivor sets are actually dangerous for the full
MGF contribution, or whether the positive tail bound is simply too pessimistic.

For each threshold on the trimmed fine layer, it reports:

    W(theta) = sum_{R>=theta} exp(lift(X32)/4) / M
    A(theta) = sum_{R>=theta} exp((lift(X32)+R)/4) / M

and their half-rate scaled versions.  The gap between W and A identifies whether
the missing theorem should be a positive weighted-tail bound or a sharper
layer-cake/cancellation statement.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)


@dataclass(frozen=True)
class Row:
    p: int
    m: int
    theta: float
    count: int
    weighted_c: float
    actual_c: float
    ratio_actual_to_weighted: float
    exact_mgf: float
    fine_max: float


def lift32_to64(x32: np.ndarray, m64: int) -> np.ndarray:
    m32 = len(x32)
    return np.array([x32[j % m32] for j in range(m64)], dtype=float)


def row_for_m(m: int, chunk: int, trim: int, tau: float, rate: float) -> Row | None:
    p = 64 * m + 1
    if not is_prime(p):
        return None
    x64 = normalized_values_vectorized(p, 64, chunk)
    x32 = normalized_values_vectorized(p, 32, chunk)
    lifted = lift32_to64(x32, len(x64))
    fine = x64 - lifted
    order = np.argsort(fine)[::-1]
    weights = np.exp(lifted * rate)
    actual_weights = np.exp(x64 * rate)
    m64 = len(fine)
    best: Row | None = None
    running_w = 0.0
    running_actual = 0.0
    for idx, j in enumerate(order[min(trim, m64) :], start=1):
        theta = float(fine[j])
        if theta <= tau:
            break
        running_w += float(weights[j])
        running_actual += float(actual_weights[j])
        scale = math.exp(theta / 2.0) / m64
        weighted_c = running_w * scale
        actual_c = running_actual * scale
        ratio = actual_c / weighted_c if weighted_c else 0.0
        candidate = Row(
            p=p,
            m=m,
            theta=theta,
            count=idx,
            weighted_c=weighted_c,
            actual_c=actual_c,
            ratio_actual_to_weighted=ratio,
            exact_mgf=float(actual_weights.mean()),
            fine_max=float(fine[order[0]]),
        )
        if best is None or candidate.actual_c > best.actual_c:
            best = candidate
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--trim", type=int, default=1)
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--max-exact-mgf", type=float, default=None)
    parser.add_argument("--sort", choices=["actual_c", "weighted_c", "ratio"], default="actual_c")
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows_all = [
        row
        for m in range(args.min_index, args.max_index + 1)
        if (row := row_for_m(m, args.chunk, args.trim, args.tau, args.rate)) is not None
    ]
    rows = [
        row for row in rows_all
        if args.max_exact_mgf is None or row.exact_mgf <= args.max_exact_mgf
    ]
    key = {
        "actual_c": lambda row: row.actual_c,
        "weighted_c": lambda row: row.weighted_c,
        "ratio": lambda row: row.ratio_actual_to_weighted,
    }[args.sort]
    rows.sort(key=key, reverse=True)

    print(
        f"R262 n=64 survivor actual mass cases={len(rows)} filtered_from={len(rows_all)} "
        f"M=[{args.min_index},{args.max_index}] trim={args.trim} tau={args.tau} "
        f"max_exact_mgf={args.max_exact_mgf} sort={args.sort}"
    )
    print("score    actualC weightedC ratio   theta  count exactMGF fineMax M      p")
    print("-" * 98)
    for row in rows[: args.top]:
        print(
            f"{key(row):<8.4f} {row.actual_c:<7.4f} {row.weighted_c:<9.4f} "
            f"{row.ratio_actual_to_weighted:<7.4f} {row.theta:<6.3f} "
            f"{row.count:<5d} {row.exact_mgf:<8.4f} {row.fine_max:<7.3f} "
            f"{row.m:<6d} {row.p}"
        )

    if rows:
        worst_actual = max(rows, key=lambda row: row.actual_c)
        worst_weighted = max(rows, key=lambda row: row.weighted_c)
        print("\nsummary")
        print(
            f"worst_actual_c={worst_actual.actual_c:.8f} M={worst_actual.m} "
            f"p={worst_actual.p} weightedC={worst_actual.weighted_c:.8f}"
        )
        print(
            f"worst_weighted_c={worst_weighted.weighted_c:.8f} M={worst_weighted.m} "
            f"p={worst_weighted.p} actualC={worst_weighted.actual_c:.8f}"
        )


if __name__ == "__main__":
    main()
