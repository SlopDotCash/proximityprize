#!/usr/bin/env python3
"""#466 R222: zero-split finite-grid budget for normalized-square spectra.

R221 shows the literal bulk envelope cannot include θ = 0.  This probe tests
the repaired R216 certificate:

    B(0) = M,
    B(θ) = C * M * exp(-θ / scale) + K       for θ > 0.

The question is not whether this proves the analytic tail.  It asks whether,
if the positive-threshold tail were true, the finite-grid weighted budget would
still fit inside the R213 quarter-MGF target.
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


def split_envelope_budget(
    carrier: int,
    step: float,
    cutoff: float,
    rate: float,
    c_bulk: float,
    scale: float,
    spike_budget: float,
    split_zero: bool,
) -> float:
    total = 0.0
    for theta, delta in staircase_deltas(step, cutoff, rate):
        if split_zero and abs(theta) < 1e-15:
            bound_per_carrier = 1.0
        else:
            bound_per_carrier = c_bulk * math.exp(-theta / scale) + spike_budget / carrier
        total += delta * bound_per_carrier
    return total


def positive_tail_worst_ratio(
    xs: list[float],
    carrier: int,
    step: float,
    cutoff: float,
    c_bulk: float,
    scale: float,
    spike_budget: float,
) -> tuple[float, float, float, float]:
    worst_ratio = 0.0
    worst_theta = 0.0
    worst_surv = 0.0
    worst_bound = 0.0
    for theta, _delta in staircase_deltas(step, cutoff, 0.25):
        if theta <= 0:
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
    parser.add_argument("--seed", type=int, default=466222)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--steps", type=float, nargs="+", default=[1.0, 0.5, 0.25, 0.125])
    parser.add_argument("--cutoff", type=float, default=32.0)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--scale", type=float, default=2.0)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--carrier", choices=["sample", "coset", "frequency"], default="coset")
    args = parser.parse_args()

    if args.mode == "exact":
        cases = exact_cases(args.max_n, args.max_p)
    else:
        cases = prize_cases(args.ns, args.samples, args.seed, args.min_index_power)

    print(
        f"R222 zero-split grid budget mode={args.mode} rate={args.rate} "
        f"C={args.c_bulk} scale={args.scale} K={args.spike_budget} carrier={args.carrier}"
    )
    print("n     sample   carrier      step   maxX    mgf      emp      unsplit  split    slack    posRatio θ")
    print("-" * 122)
    best_split = (math.inf, None)
    worst_pos = (0.0, None)
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
            unsplit = split_envelope_budget(
                carrier, step, cutoff, args.rate, args.c_bulk, args.scale, args.spike_budget, False
            )
            split = split_envelope_budget(
                carrier, step, cutoff, args.rate, args.c_bulk, args.scale, args.spike_budget, True
            )
            pos_ratio, pos_theta, _pos_surv, _pos_bound = positive_tail_worst_ratio(
                xs, carrier, step, cutoff, args.c_bulk, args.scale, args.spike_budget
            )
            if split < best_split[0]:
                best_split = (split, (n, p, step, label))
            if pos_ratio > worst_pos[0]:
                worst_pos = (pos_ratio, (n, p, step, pos_theta, label))
            print(
                f"{n:<5d} {len(xs):<8d} {carrier:<12d} {step:<6.3g} {max(xs):<7.3f} "
                f"{direct_mgf(xs, args.rate):<8.4f} {emp:<8.4f} {unsplit:<8.4f} "
                f"{split:<8.4f} {2.0 - split:<8.4f} {pos_ratio:<8.4f} {pos_theta:<5.2f} {label}"
            )

    print("\nsummary")
    print(f"tested_cases={len(cases)} steps={len(args.steps)}")
    if best_split[1] is not None:
        split, (n, p, step, label) = best_split
        print(f"best_split_budget={split:.6f} slack={2-split:.6f} n={n} p={p} step={step} {label}")
    if worst_pos[1] is not None:
        ratio, (n, p, step, theta, label) = worst_pos
        print(f"worst_positive_tail_ratio={ratio:.6f} n={n} p={p} step={step} theta={theta:.3f} {label}")


if __name__ == "__main__":
    main()
