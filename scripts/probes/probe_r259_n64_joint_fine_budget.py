#!/usr/bin/env python3
"""#466 R259: joint MGF budget for X_64 = lift(X_32) + R_fine.

R258 found that deleting one fine residual spike makes R_fine have a small
half-rate tail.  A crude product MGF bound for X_32 and R_fine would overpay.
This probe uses the exact lifted X_32 values and only envelopes the trimmed
fine residual conditional on those values:

    exp((X32 + R)/4) = exp(X32/4) * exp(R/4).

After paying the top `trim` fine residual rows exactly, the residual envelope
uses the actual average weight exp(X32/4) over the remaining carrier:

    mean exp(X32/4) * envelope_Rfine.

This is still empirical/proof-design evidence, but it tests the right joint
shape rather than independent worst-case products.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r217_normalized_sq_grid_budget import staircase_deltas  # noqa: E402
from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)


@dataclass(frozen=True)
class Row:
    p: int
    m: int
    exact_full_mgf: float
    budget: float
    slack: float
    paid: float
    envelope: float
    coarse_weight_mean: float
    c_tail: float
    c_weighted_tail: float
    theta_tail: float
    count_tail: int
    fine_max: float


def lift32_to64(x32: np.ndarray, m64: int) -> np.ndarray:
    m32 = len(x32)
    return np.array([x32[j % m32] for j in range(m64)], dtype=float)


def fine_tail_constant(fine_desc: np.ndarray, tau: float, trim: int) -> tuple[float, float, int]:
    m = len(fine_desc)
    best = (0.0, tau, 0)
    for idx, value in enumerate(fine_desc[min(trim, m) :], start=1):
        theta = float(value)
        if theta <= tau:
            break
        c = (idx / m) * math.exp(theta / 2.0)
        if c > best[0]:
            best = (c, theta, idx)
    return best


def weighted_fine_tail_constant(
    fine: np.ndarray, weights: np.ndarray, order: np.ndarray, tau: float, trim: int
) -> tuple[float, float, int]:
    m = len(fine)
    best = (0.0, tau, 0)
    running = 0.0
    for idx, j in enumerate(order[min(trim, m) :], start=1):
        theta = float(fine[j])
        if theta <= tau:
            break
        running += float(weights[j])
        c = (running / m) * math.exp(theta / 2.0)
        if c > best[0]:
            best = (c, theta, idx)
    return best


def residual_envelope_budget(step: float, cutoff: float, rate: float, tau: float, c_tail: float) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        bound = 1.0 if theta <= tau + 1e-15 else c_tail * math.exp(-theta / 2.0)
        total += delta * bound
    return total


def row_for_m(m: int, chunk: int, trim: int, tau: float, step: float, rate: float) -> Row | None:
    p = 64 * m + 1
    if not is_prime(p):
        return None
    x64 = normalized_values_vectorized(p, 64, chunk)
    x32 = normalized_values_vectorized(p, 32, chunk)
    lifted = lift32_to64(x32, len(x64))
    fine = x64 - lifted
    order = np.argsort(fine)[::-1]
    paid_idx = order[: min(trim, len(order))]
    residual_idx = order[min(trim, len(order)) :]
    fine_desc = fine[order]
    c_tail, theta_tail, count_tail = fine_tail_constant(fine_desc, tau, trim)
    weights = np.exp(lifted * rate)
    c_weighted_tail, theta_weighted, count_weighted = weighted_fine_tail_constant(
        fine, weights, order, tau, trim
    )

    paid = float(np.exp((lifted[paid_idx] + fine[paid_idx]) * rate).sum() / len(fine)) if len(paid_idx) else 0.0
    coarse_weight_mean = float(weights[residual_idx].mean()) if len(residual_idx) else 0.0
    cutoff = max(0.0, float(fine[residual_idx].max()) if len(residual_idx) else 0.0)
    envelope = coarse_weight_mean * residual_envelope_budget(step, cutoff, rate, tau, c_tail)
    budget = paid + envelope
    exact = float(np.exp(x64 * rate).mean())
    return Row(
        p=p,
        m=m,
        exact_full_mgf=exact,
        budget=budget,
        slack=2.0 - budget,
        paid=paid,
        envelope=envelope,
        coarse_weight_mean=coarse_weight_mean,
        c_tail=c_tail,
        c_weighted_tail=c_weighted_tail,
        theta_tail=theta_weighted if c_weighted_tail >= c_tail else theta_tail,
        count_tail=count_weighted if c_weighted_tail >= c_tail else count_tail,
        fine_max=float(fine_desc[0]),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--max-index", type=int, default=12000)
    parser.add_argument("--chunk", type=int, default=8192)
    parser.add_argument("--trim", type=int, default=1)
    parser.add_argument("--tau", type=float, default=0.5)
    parser.add_argument("--step", type=float, default=0.03125)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--max-exact-mgf", type=float, default=None)
    parser.add_argument(
        "--sort",
        choices=["budget", "c_weighted_tail", "c_tail", "exact"],
        default="budget",
    )
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    rows_all = [
        row
        for m in range(args.min_index, args.max_index + 1)
        if (row := row_for_m(m, args.chunk, args.trim, args.tau, args.step, args.rate)) is not None
    ]
    rows = [
        row for row in rows_all
        if args.max_exact_mgf is None or row.exact_full_mgf <= args.max_exact_mgf
    ]
    sort_key = {
        "budget": lambda row: row.budget,
        "c_weighted_tail": lambda row: row.c_weighted_tail,
        "c_tail": lambda row: row.c_tail,
        "exact": lambda row: row.exact_full_mgf,
    }[args.sort]
    rows.sort(key=sort_key, reverse=True)

    print(
        f"R259 n=64 joint fine budget cases={len(rows)} filtered_from={len(rows_all)} "
        f"M=[{args.min_index},{args.max_index}] trim={args.trim} tau={args.tau} "
        f"step={args.step} max_exact_mgf={args.max_exact_mgf} sort={args.sort}"
    )
    print("budget  slack   exact   paid    env     Ew32    Ctail   CWtail  theta  count fineMax M      p")
    print("-" * 112)
    for row in rows[: args.top]:
        print(
            f"{row.budget:<7.4f} {row.slack:<7.4f} {row.exact_full_mgf:<7.4f} "
            f"{row.paid:<7.4f} {row.envelope:<7.4f} {row.coarse_weight_mean:<7.4f} "
            f"{row.c_tail:<7.4f} {row.c_weighted_tail:<7.4f} "
            f"{row.theta_tail:<6.3f} {row.count_tail:<5d} "
            f"{row.fine_max:<7.3f} {row.m:<6d} {row.p}"
        )

    print("\nsummary")
    feasible = [row for row in rows if row.budget <= 2.0 + 1e-12]
    print(f"feasible_rows={len(feasible)}")
    if rows:
        worst = max(rows, key=lambda row: row.budget)
        worst_weighted = max(rows, key=lambda row: row.c_weighted_tail)
        print(
            f"worst_budget={worst.budget:.8f} slack={worst.slack:.8f} "
            f"M={worst.m} p={worst.p} exact={worst.exact_full_mgf:.8f}"
        )
        print(
            f"worst_weighted_tail={worst_weighted.c_weighted_tail:.8f} "
            f"M={worst_weighted.m} p={worst_weighted.p} "
            f"budget={worst_weighted.budget:.8f}"
        )


if __name__ == "__main__":
    main()
