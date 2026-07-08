#!/usr/bin/env python3
"""#466 R224: required bulk constant above a low-band cutoff.

R223 makes the analytic target:

    #{X_b >= theta} <= C * M * exp(-theta / scale) + K,  theta > tau.

This probe computes the smallest empirical/exact C required for a grid of tau
and scale values.  It separates the low-band bookkeeping question from the
actual distributional theorem we would need to prove.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r217_normalized_sq_grid_budget import (  # noqa: E402
    exact_cases,
    prize_cases,
)


def threshold_grid(step: float, cutoff: float) -> list[float]:
    return [j * step for j in range(max(0, math.ceil(cutoff / step)) + 1)]


def required_c_above(
    xs: list[float],
    carrier: int,
    step: float,
    cutoff: float,
    tau: float,
    scale: float,
    spike_budget: float,
) -> tuple[float, float, float, float]:
    worst_c = 0.0
    worst_theta = 0.0
    worst_surv = 0.0
    worst_residual = 0.0
    spike = spike_budget / carrier
    for theta in threshold_grid(step, cutoff):
        if theta <= tau + 1e-15:
            continue
        surv = sum(1 for x in xs if theta <= x) / len(xs)
        residual = max(0.0, surv - spike)
        need = residual * math.exp(theta / scale)
        if need > worst_c:
            worst_c = need
            worst_theta = theta
            worst_surv = surv
            worst_residual = residual
    return worst_c, worst_theta, worst_surv, worst_residual


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exact", "prize"], default="exact")
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=466224)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--step", type=float, default=0.125)
    parser.add_argument("--taus", type=float, nargs="+", default=[0, 0.25, 0.5, 0.75, 1, 1.5, 2])
    parser.add_argument("--scales", type=float, nargs="+", default=[1.5, 2.0, 2.5, 3.0])
    parser.add_argument("--cutoff", type=float, default=32.0)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--carrier", choices=["sample", "coset", "frequency"], default="coset")
    args = parser.parse_args()

    cases = exact_cases(args.max_n, args.max_p) if args.mode == "exact" else prize_cases(
        args.ns, args.samples, args.seed, args.min_index_power
    )

    print(
        f"R224 above-band required-C mode={args.mode} step={args.step} "
        f"K={args.spike_budget} carrier={args.carrier}"
    )
    print("n     sample   carrier      tau    " + " ".join(f"C@{s:g} θ" for s in args.scales) + " label")
    print("-" * 132)
    global_worst = {scale: (0.0, None) for scale in args.scales}
    for label, n, p, coset_pop, freq_pop, xs in cases:
        if args.carrier == "sample":
            carrier = len(xs)
        elif args.carrier == "coset":
            carrier = coset_pop
        else:
            carrier = freq_pop
        cutoff = max(args.cutoff, max(xs))
        for tau in args.taus:
            cells = []
            for scale in args.scales:
                need, theta, surv, residual = required_c_above(
                    xs, carrier, args.step, cutoff, tau, scale, args.spike_budget
                )
                cells.append(f"{need:.4f} {theta:.2f}")
                if need > global_worst[scale][0]:
                    global_worst[scale] = (need, (n, p, tau, theta, surv, residual, label))
            print(f"{n:<5d} {len(xs):<8d} {carrier:<12d} {tau:<6.3g} " + " ".join(f"{c:<12s}" for c in cells) + f" {label}")

    print("\nsummary")
    print(f"tested_cases={len(cases)} taus={len(args.taus)} scales={len(args.scales)}")
    for scale in args.scales:
        need, witness = global_worst[scale]
        if witness is None:
            continue
        n, p, tau, theta, surv, residual, label = witness
        print(
            f"global_required_C scale={scale:g} C={need:.6f} "
            f"tau={tau:.3f} theta={theta:.3f} surv={surv:.6g} residual={residual:.6g} "
            f"n={n} p={p} {label}"
        )


if __name__ == "__main__":
    main()
