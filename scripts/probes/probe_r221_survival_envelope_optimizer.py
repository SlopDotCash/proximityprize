#!/usr/bin/env python3
"""#466 R221: optimize normalized-square survival envelopes.

R216/R217 use a concrete survival law for

    X_b = |eta_G(b)|^2 / sigma^2

over the nonzero/coset carrier:

    #{X_b >= theta} <= C * M * exp(-theta / scale) + K.

R218 showed that moment Markov alone cannot certify the low/mid thresholds.
This probe measures the best constants for exponential survival envelopes,
both on exact small spectra and on prize-index random samples.
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r199_vectorized_large_anchor_tail import (  # noqa: E402
    normalized_values_vectorized,
)
from scripts.probes.probe_r206_prize_index_random_sampling import (  # noqa: E402
    next_prime_congruent_one,
    normalized_samples,
)


@dataclass(frozen=True)
class Case:
    label: str
    n: int
    p: int
    carrier: int
    xs: list[float]


def exact_cases(max_n: int, max_p: int) -> list[Case]:
    anchors = [
        (16, 193, "floor-near"),
        (32, 1153, "small-index"),
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16778497, "shared-prime"),
    ]
    out: list[Case] = []
    for n, p, label in anchors:
        if n <= max_n and p <= max_p and (p - 1) % n == 0:
            xs = list(normalized_values_vectorized(p, n, 32768))
            out.append(Case(label, n, p, (p - 1) // n, xs))
    return out


def prize_cases(ns: list[int], samples: int, seed: int, min_index_power: int) -> list[Case]:
    out: list[Case] = []
    min_index = 2**min_index_power
    for offset, n in enumerate(ns):
        p, m = next_prime_congruent_one(n, min_index)
        xs = normalized_samples(p, n, samples, seed + offset)
        out.append(Case(f"prize M_offset={m - min_index}", n, p, m, xs))
    return out


def thresholds(step: float, cutoff: float) -> list[float]:
    count = max(0, math.ceil(cutoff / step))
    return [j * step for j in range(count + 1)]


def survival_fraction(xs: list[float], theta: float) -> float:
    return sum(1 for x in xs if theta <= x) / len(xs)


def required_c(xs: list[float], carrier: int, scale: float, spike_budget: float, step: float, cutoff: float) -> tuple[float, float]:
    worst = 0.0
    worst_theta = 0.0
    spike = spike_budget / carrier
    for theta in thresholds(step, cutoff):
        surv = survival_fraction(xs, theta)
        residual = max(0.0, surv - spike)
        need = residual * math.exp(theta / scale)
        if need > worst:
            worst = need
            worst_theta = theta
    return worst, worst_theta


def envelope_ok(xs: list[float], carrier: int, c_bulk: float, scale: float, spike_budget: float, step: float, cutoff: float) -> tuple[bool, float, float, float]:
    worst_ratio = 0.0
    worst_theta = 0.0
    worst_surv = 0.0
    for theta in thresholds(step, cutoff):
        surv = survival_fraction(xs, theta)
        bound = c_bulk * math.exp(-theta / scale) + spike_budget / carrier
        ratio = surv / bound if bound > 0 else math.inf
        if ratio > worst_ratio:
            worst_ratio = ratio
            worst_theta = theta
            worst_surv = surv
    return worst_ratio <= 1.0 + 1e-12, worst_ratio, worst_theta, worst_surv


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exact", "prize"], default="prize")
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512, 1024])
    parser.add_argument("--samples", type=int, default=30000)
    parser.add_argument("--seed", type=int, default=466221)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--step", type=float, default=0.25)
    parser.add_argument("--cutoff", type=float, default=24.0)
    parser.add_argument("--scales", type=float, nargs="+", default=[1.0, 1.5, 2.0, 2.5, 3.0])
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--scale", type=float, default=2.0)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    args = parser.parse_args()

    cases = exact_cases(args.max_n, args.max_p) if args.mode == "exact" else prize_cases(
        args.ns, args.samples, args.seed, args.min_index_power
    )

    print(
        f"R221 survival-envelope optimizer mode={args.mode} step={args.step} "
        f"cutoff={args.cutoff} K={args.spike_budget}"
    )
    print("n     sample   carrier      maxX    meanX   live_ok live_ratio theta  surv    " + " ".join(f"C@{s:g}" for s in args.scales))
    print("-" * 132)
    global_needs = {scale: (0.0, None) for scale in args.scales}
    worst_live = (0.0, None)
    for case in cases:
        cutoff = max(args.cutoff, max(case.xs))
        live_ok, live_ratio, live_theta, live_surv = envelope_ok(
            case.xs, case.carrier, args.c_bulk, args.scale, args.spike_budget, args.step, cutoff
        )
        if live_ratio > worst_live[0]:
            worst_live = (live_ratio, case)
        needs = []
        for scale in args.scales:
            need, theta = required_c(case.xs, case.carrier, scale, args.spike_budget, args.step, cutoff)
            needs.append(need)
            if need > global_needs[scale][0]:
                global_needs[scale] = (need, (case, theta))
        print(
            f"{case.n:<5d} {len(case.xs):<8d} {case.carrier:<12d} {max(case.xs):<7.3f} "
            f"{sum(case.xs)/len(case.xs):<7.3f} {str(live_ok):<7s} {live_ratio:<10.4f} "
            f"{live_theta:<6.2f} {live_surv:<7.4f} "
            + " ".join(f"{need:<8.4f}" for need in needs)
            + f" {case.label}"
        )

    print("\nsummary")
    print(f"tested={len(cases)}")
    ratio, case = worst_live
    if case is not None:
        print(f"live_envelope_worst_ratio={ratio:.6f} n={case.n} p={case.p} label={case.label}")
    for scale in args.scales:
        need, witness = global_needs[scale]
        if witness is None:
            continue
        case, theta = witness
        print(
            f"required_C scale={scale:g} C={need:.6f} "
            f"theta={theta:.3f} n={case.n} p={case.p} label={case.label}"
        )


if __name__ == "__main__":
    main()
