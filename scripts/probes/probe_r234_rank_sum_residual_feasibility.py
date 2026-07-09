#!/usr/bin/env python3
"""#466 R234: direct rank-sum plus residual-tail feasibility.

R231 paid trimmed top spikes through a staircase count budget, which greatly
overcharges a finite set of high ranks.  R230/R232 suggest a sharper proof
shape:

* prove a direct rank-sum cap for the top `L` quotient orbits,
    sum_{r < L} exp(X_(r)/4) / M <= A_L;
* prove an exponential survival envelope only for the residual spectrum;
* combine the direct top cap with the residual envelope budget.

This probe computes the empirical version of that proof shape.  It reports
the worst direct top-rank contribution, the worst residual tail constant, and
the resulting closed budget over exact medium spectra.
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
class Case:
    n: int
    p: int
    m: int
    desc: np.ndarray
    label: str


def medium_cases(
    min_a: int,
    max_a: int,
    min_index: int,
    max_index: int,
    min_beta: float,
    chunk: int,
) -> list[Case]:
    out: list[Case] = []
    for a in range(min_a, max_a + 1):
        n = 2**a
        beta_floor = 2 if min_beta <= 0 else math.ceil(n ** (min_beta - 1.0))
        lo = max(2, min_index, beta_floor)
        for m in range(lo, max_index + 1):
            p = m * n + 1
            if is_prime(p):
                xs = normalized_values_vectorized(p, n, chunk)
                out.append(Case(n, p, len(xs), np.sort(xs)[::-1], f"a={a}-M={m}"))
    return out


def direct_top_mgf(desc: np.ndarray, trim: int) -> float:
    top = desc[: min(trim, len(desc))]
    if len(top) == 0:
        return 0.0
    return float(np.exp(top / 4.0).sum() / len(desc))


def residual_required_c(
    desc: np.ndarray, trim: int, tau: float, spike_budget: float
) -> tuple[float, float, int]:
    residual = desc[min(trim, len(desc)) :]
    m = len(desc)
    best_c = 0.0
    best_theta = tau
    best_count = 0
    for idx, x0 in enumerate(residual):
        theta = float(x0)
        if theta <= tau:
            break
        count = idx + 1
        c_req = max(0.0, (count - spike_budget) / m) * math.exp(theta / 2.0)
        if c_req > best_c:
            best_c = c_req
            best_theta = theta
            best_count = count
    return best_c, best_theta, best_count


def residual_budget(
    carrier: int,
    trim: int,
    step: float,
    cutoff: float,
    rate: float,
    tau: float,
    c_bulk: float,
    spike_budget: float,
) -> float:
    residual_fraction = max(0.0, (carrier - trim) / carrier)
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if theta <= tau + 1.0e-15:
            bound = residual_fraction
        else:
            bound = c_bulk * math.exp(-theta / 2.0) + spike_budget / carrier
        total += delta * bound
    return total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-min-a", type=int, default=3)
    parser.add_argument("--medium-max-a", type=int, default=8)
    parser.add_argument("--min-index", type=int, default=512)
    parser.add_argument("--medium-max-index", type=int, default=4096)
    parser.add_argument("--min-beta", type=float, default=0.0)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--trims", type=int, nargs="+", default=[1, 2, 4, 8, 16, 32, 64])
    parser.add_argument("--taus", type=float, nargs="+", default=[0.5, 1.0, 2.0, 4.0])
    parser.add_argument("--spike-budgets", type=float, nargs="+", default=[0.0, 1.0, 2.0])
    parser.add_argument("--step", type=float, default=0.125)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--cutoff", type=float, default=0.0)
    parser.add_argument("--top", type=int, default=30)
    args = parser.parse_args()

    cases = medium_cases(
        args.medium_min_a,
        args.medium_max_a,
        args.min_index,
        args.medium_max_index,
        args.min_beta,
        args.chunk,
    )
    rows = []
    for trim in args.trims:
        top_witness = max(cases, key=lambda case: direct_top_mgf(case.desc, trim))
        top_cap = direct_top_mgf(top_witness.desc, trim)
        for tau in args.taus:
            for spike_budget in args.spike_budgets:
                c_req = 0.0
                c_witness = None
                c_theta = tau
                c_count = 0
                for case in cases:
                    c, theta, count = residual_required_c(case.desc, trim, tau, spike_budget)
                    if c > c_req:
                        c_req = c
                        c_theta = theta
                        c_count = count
                        c_witness = case
                worst_budget = -1.0
                b_witness = None
                for case in cases:
                    cutoff = max(args.cutoff, float(case.desc[0]))
                    budget = top_cap + residual_budget(
                        case.m, trim, args.step, cutoff, args.rate, tau, c_req, spike_budget
                    )
                    if budget > worst_budget:
                        worst_budget = budget
                        b_witness = case
                rows.append(
                    (
                        worst_budget,
                        top_cap,
                        c_req,
                        trim,
                        tau,
                        spike_budget,
                        c_theta,
                        c_count,
                        top_witness,
                        c_witness,
                        b_witness,
                    )
                )

    rows.sort(key=lambda row: (row[0], row[2], row[1]))
    print(
        "R234 rank-sum residual feasibility "
        f"cases={len(cases)} step={args.step} rate={args.rate} min_beta={args.min_beta}"
    )
    print(
        "budget   slack    topCap   C_req    trim tau   K     theta        count "
        "topW(n,p,M)        Cwit(n,p,M)        Bwit(n,p,M)"
    )
    print("-" * 150)
    for budget, top_cap, c_req, trim, tau, spike_budget, theta, count, topw, cw, bw in rows[: args.top]:
        top_desc = f"{topw.n},{topw.p},{topw.m}"
        c_desc = "-" if cw is None else f"{cw.n},{cw.p},{cw.m}"
        b_desc = "-" if bw is None else f"{bw.n},{bw.p},{bw.m}"
        print(
            f"{budget:<8.4f} {2-budget:<8.4f} {top_cap:<8.4f} {c_req:<8.5f} "
            f"{trim:<5d} {tau:<5.2f} {spike_budget:<5.1f} {theta:<12.6f} {count:<5d} "
            f"{top_desc:<18s} {c_desc:<18s} {b_desc}"
        )

    print("\nsummary")
    feasible = [row for row in rows if row[0] <= 2.0 + 1.0e-9]
    print(f"feasible_rows={len(feasible)}")
    if rows:
        best = rows[0]
        print(
            f"best_budget={best[0]:.6f} slack={2-best[0]:.6f} topCap={best[1]:.6f} "
            f"C_req={best[2]:.8f} trim={best[3]} tau={best[4]} K={best[5]}"
        )


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(130)
