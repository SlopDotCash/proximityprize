#!/usr/bin/env python3
"""#466 R223: low-band exact payment for normalized-square survival grids.

R222 showed that paying only θ = 0 exactly leaves the positive tail failing at
the first grid point.  This probe pays every threshold θ <= tau by the full
carrier, then uses the proposed bulk-plus-spikes exponential envelope above tau.

The target is still the R213/R216 quarter-MGF budget:

    Σ_θ δ(θ) B(θ) <= 2 * carrier.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r217_normalized_sq_grid_budget import (  # noqa: E402
    direct_mgf,
    empirical_budget,
    exact_cases,
    prize_cases,
    staircase_deltas,
)


def low_band_budget(
    carrier: int,
    step: float,
    cutoff: float,
    rate: float,
    tau: float,
    c_bulk: float,
    scale: float,
    spike_budget: float,
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if theta <= tau + 1e-15:
            bound_per_carrier = 1.0
        else:
            bound_per_carrier = c_bulk * math.exp(-theta / scale) + spike_budget / carrier
        total += delta * bound_per_carrier
    return total


def above_band_worst_ratio(
    xs: list[float],
    carrier: int,
    step: float,
    cutoff: float,
    tau: float,
    c_bulk: float,
    scale: float,
    spike_budget: float,
) -> tuple[float, float, float, float]:
    worst_ratio = 0.0
    worst_theta = 0.0
    worst_surv = 0.0
    worst_bound = 0.0
    for theta, _delta in staircase_deltas(step, cutoff, 0.25):
        if theta <= tau + 1e-15:
            continue
        surv = sum(1 for x in xs if theta <= x) / len(xs)
        bound = c_bulk * math.exp(-theta / scale) + spike_budget / carrier
        ratio = surv / bound if bound > 0 else math.inf
        if ratio > worst_ratio:
            worst_ratio = ratio
            worst_theta = theta
            worst_surv = surv
            worst_bound = bound
    return worst_ratio, worst_theta, worst_surv, worst_bound


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exact", "prize"], default="prize")
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=466223)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--steps", type=float, nargs="+", default=[0.5, 0.25, 0.125])
    parser.add_argument("--taus", type=float, nargs="+", default=[0.0, 0.125, 0.25, 0.5, 0.75, 1.0])
    parser.add_argument("--cutoff", type=float, default=32.0)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--scale", type=float, default=2.0)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--carrier", choices=["sample", "coset", "frequency"], default="coset")
    args = parser.parse_args()

    cases = exact_cases(args.max_n, args.max_p) if args.mode == "exact" else prize_cases(
        args.ns, args.samples, args.seed, args.min_index_power
    )

    print(
        f"R223 low-band split budget mode={args.mode} rate={args.rate} "
        f"C={args.c_bulk} scale={args.scale} K={args.spike_budget} carrier={args.carrier}"
    )
    print("n     sample   carrier      step   tau    maxX    mgf      emp      budget   slack    tailRatio θ")
    print("-" * 126)
    best = (math.inf, None)
    worst_tail = (0.0, None)
    viable = []
    for label, n, p, coset_pop, freq_pop, xs in cases:
        if args.carrier == "sample":
            carrier = len(xs)
        elif args.carrier == "coset":
            carrier = coset_pop
        else:
            carrier = freq_pop
        for step in args.steps:
            cutoff = max(args.cutoff, max(xs))
            emp = empirical_budget(xs, step, cutoff, args.rate)
            mgf = direct_mgf(xs, args.rate)
            for tau in args.taus:
                budget = low_band_budget(
                    carrier, step, cutoff, args.rate, tau, args.c_bulk, args.scale, args.spike_budget
                )
                ratio, theta, _surv, _bound = above_band_worst_ratio(
                    xs, carrier, step, cutoff, tau, args.c_bulk, args.scale, args.spike_budget
                )
                slack = 2.0 - budget
                ok = slack >= -1e-12 and ratio <= 1.0 + 1e-12
                if budget < best[0]:
                    best = (budget, (n, p, step, tau, ratio, label))
                if ratio > worst_tail[0]:
                    worst_tail = (ratio, (n, p, step, tau, theta, label))
                if ok:
                    viable.append((n, p, step, tau, budget, ratio, label))
                print(
                    f"{n:<5d} {len(xs):<8d} {carrier:<12d} {step:<6.3g} {tau:<6.3g} "
                    f"{max(xs):<7.3f} {mgf:<8.4f} {emp:<8.4f} {budget:<8.4f} "
                    f"{slack:<8.4f} {ratio:<9.4f} {theta:<5.2f} {label}"
                )

    print("\nsummary")
    print(f"tested_cases={len(cases)} steps={len(args.steps)} taus={len(args.taus)} viable_rows={len(viable)}")
    if best[1] is not None:
        budget, (n, p, step, tau, ratio, label) = best
        print(
            f"best_budget={budget:.6f} slack={2-budget:.6f} tailRatio={ratio:.6f} "
            f"n={n} p={p} step={step} tau={tau} {label}"
        )
    if worst_tail[1] is not None:
        ratio, (n, p, step, tau, theta, label) = worst_tail
        print(f"worst_tail_ratio={ratio:.6f} n={n} p={p} step={step} tau={tau} theta={theta:.3f} {label}")
    if viable:
        n, p, step, tau, budget, ratio, label = min(viable, key=lambda row: (row[4], row[2], row[3]))
        print(
            f"best_viable budget={budget:.6f} slack={2-budget:.6f} tailRatio={ratio:.6f} "
            f"n={n} p={p} step={step} tau={tau} {label}"
        )


if __name__ == "__main__":
    main()
