#!/usr/bin/env python3
"""#466 R213: fit exponential tail rates in the actual prize-index regime.

R212 isolates the large-index child law with the conservative R189 tail

    N(T) <= 0.6 * S * exp(-T/2) + 2.

This probe samples the actual prize-index regime M >= 2^128 and asks how much
room there is in that law.  For several candidate rates alpha it reports the
least sampled bulk constant C needed in

    N(T) <= C * S * exp(-alpha*T) + K

over the sampled thresholds.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r206_prize_index_random_sampling import (  # noqa: E402
    next_prime_congruent_one,
    normalized_samples,
)


def required_bulk_constant(xs: list[float], alpha: float, spike_budget: float, step: float) -> tuple[float, float, int]:
    """Return worst sampled C, threshold, count for N(T) <= C*S*exp(-alpha*T)+K."""
    s = len(xs)
    max_x = max(xs)
    worst_c = 0.0
    worst_theta = 0.0
    worst_count = 0
    j = 2
    while j * step <= max_x + 1e-12:
        theta = j * step
        count = sum(1 for x in xs if theta <= x)
        need = max(0.0, count - spike_budget) / (s * math.exp(-alpha * theta))
        if need > worst_c:
            worst_c = need
            worst_theta = theta
            worst_count = count
        j += 1
    return worst_c, worst_theta, worst_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=466213)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--rates", type=float, nargs="+", default=[0.5, 0.625, 0.75, 1.0])
    args = parser.parse_args()

    min_index = 2 ** args.min_index_power
    print(
        f"R213 prize-index tail-rate fit samples={args.samples} "
        f"min_index=2^{args.min_index_power} K={args.spike_budget}"
    )
    print("n     M_offset  mgf1/4  maxX    meanX   " + "  ".join(f"C@a={a:g}" for a in args.rates))
    print("-" * 120)

    global_worst = {alpha: (0.0, 0, 0, 0.0, 0) for alpha in args.rates}
    for offset, n in enumerate(args.ns):
        p, m = next_prime_congruent_one(n, min_index)
        xs = normalized_samples(p, n, args.samples, args.seed + offset)
        mgf4 = sum(math.exp(x / 4) for x in xs) / len(xs)
        mean_x = sum(xs) / len(xs)
        row = []
        for alpha in args.rates:
            c, theta, count = required_bulk_constant(xs, alpha, args.spike_budget, args.step)
            row.append(c)
            if c > global_worst[alpha][0]:
                global_worst[alpha] = (c, n, m - min_index, theta, count)
        print(
            f"{n:<5d} {m - min_index:<9d} {mgf4:<7.4f} {max(xs):<7.3f} {mean_x:<7.4f} "
            + "  ".join(f"{c:<8.4f}" for c in row)
        )

    print("\nsummary")
    for alpha in args.rates:
        c, n, offset, theta, count = global_worst[alpha]
        print(
            f"rate={alpha:g} worst_C={c:.6f} n={n} M_offset={offset} "
            f"T={theta:.2f} count={count}"
        )


if __name__ == "__main__":
    main()
