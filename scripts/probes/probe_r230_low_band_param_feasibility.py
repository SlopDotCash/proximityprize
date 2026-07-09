#!/usr/bin/env python3
"""#466 R230: feasibility scan for parameterized low-band quotient tails.

R230's formal socket asks for constants `tau, Cbulk, Kquot` such that above
the low band

    N_q(theta) <= Cbulk * M * exp(-theta/2) + Kquot

and the resulting low-band staircase budget stays below the quarter-MGF target
`2`.  This probe uses exact quotient spectra and reports, for each candidate
`(tau, Kquot)`, the worst required `Cbulk` and the closed budget at that
required constant.
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
    xs: np.ndarray
    label: str


def medium_cases(max_a: int, max_index: int, min_index: int, chunk: int) -> list[Case]:
    out: list[Case] = []
    for a in range(3, max_a + 1):
        n = 2**a
        for m in range(max(2, min_index), max_index + 1):
            p = m * n + 1
            if is_prime(p):
                out.append(Case(n, p, m, normalized_values_vectorized(p, n, chunk), f"a={a}-M={m}"))
    return out


def required_c(xs: np.ndarray, tau: float, spike_budget: float) -> tuple[float, float, int]:
    desc = np.sort(xs)[::-1]
    m = len(desc)
    best_c = 0.0
    best_theta = tau
    best_count = 0
    for idx, x0 in enumerate(desc):
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


def low_band_budget(
    carrier: int,
    step: float,
    cutoff: float,
    rate: float,
    tau: float,
    c_bulk: float,
    spike_budget: float,
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if theta <= tau + 1.0e-15:
            bound = 1.0
        else:
            bound = c_bulk * math.exp(-theta / 2.0) + spike_budget / carrier
        total += delta * bound
    return total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--medium-max-a", type=int, default=10)
    parser.add_argument("--medium-max-index", type=int, default=512)
    parser.add_argument("--min-index", type=int, default=2)
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--taus", type=float, nargs="+", default=[0.5, 0.75, 1.0, 1.25, 1.5])
    parser.add_argument("--spike-budgets", type=float, nargs="+", default=[2.0, 3.0, 4.0, 6.0])
    parser.add_argument("--step", type=float, default=0.25)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--cutoff", type=float, default=32.0)
    parser.add_argument("--top", type=int, default=24)
    args = parser.parse_args()

    cases = medium_cases(args.medium_max_a, args.medium_max_index, args.min_index, args.chunk)
    rows = []
    for tau in args.taus:
        for spike_budget in args.spike_budgets:
            worst = (0.0, tau, 0, None)
            for case in cases:
                c_req, theta, count = required_c(case.xs, tau, spike_budget)
                if c_req > worst[0]:
                    worst = (c_req, theta, count, case)
            worst_budget = -1.0
            for case in cases:
                cutoff = max(args.cutoff, float(case.xs.max()))
                budget = low_band_budget(
                    case.m, args.step, cutoff, args.rate, tau, worst[0], spike_budget
                )
                worst_budget = max(worst_budget, budget)
            rows.append((worst[0], worst_budget, tau, spike_budget, worst[1], worst[2], worst[3]))

    rows.sort(key=lambda row: (row[1], row[0]))
    print(
        "R230 low-band param feasibility "
        f"cases={len(cases)} step={args.step} rate={args.rate} cutoff>={args.cutoff}"
    )
    print("budget   slack    C_req    tau   K      witness_theta count  M      n     p          label")
    print("-" * 116)
    for c_req, budget, tau, spike_budget, theta, count, case in rows[: args.top]:
        label = "" if case is None else case.label
        n = 0 if case is None else case.n
        p = 0 if case is None else case.p
        m = 0 if case is None else case.m
        print(
            f"{budget:<8.4f} {2-budget:<8.4f} {c_req:<8.5f} {tau:<5.2f} {spike_budget:<6.1f} "
            f"{theta:<13.6f} {count:<6d} {m:<6d} {n:<5d} {p:<10d} {label}"
        )

    print("\nsummary")
    feasible = [row for row in rows if row[1] <= 2.0 + 1e-9]
    print(f"feasible_rows={len(feasible)}")
    if rows:
        best = rows[0]
        print(
            f"best_budget={best[1]:.6f} slack={2-best[1]:.6f} "
            f"C_req={best[0]:.8f} tau={best[2]} K={best[3]}"
        )


if __name__ == "__main__":
    main()
