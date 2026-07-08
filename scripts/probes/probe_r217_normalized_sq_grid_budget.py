#!/usr/bin/env python3
"""#466 R217: finite-grid budget for the normalized-square MGF residual.

R216 reduces the live normalized-square residual to a finite threshold grid:

    sum_theta delta(theta) * B(theta) <= 2 * S,

where `B(theta)` is a survival-count ceiling for

    X_b = |eta_G(b)|^2 / sigma^2,  b != 0.

The empirical tail target is the half-rate bulk-plus-two envelope

    B(theta) = C * S * exp(-theta/2) + K.

This probe builds the explicit staircase used by the Lean statement and checks
both:

* the empirical count-weighted certificate on sampled or exact spectra;
* the closed envelope budget with `C=0.6, K=2`.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r199_vectorized_large_anchor_tail import (  # noqa: E402
    normalized_values_vectorized,
)
from scripts.probes.probe_r206_prize_index_random_sampling import (  # noqa: E402
    next_prime_congruent_one,
    normalized_samples,
)


def staircase_thresholds(step: float, cutoff: float) -> list[float]:
    if step <= 0:
        raise ValueError("step must be positive")
    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    kmax = max(0, math.ceil(cutoff / step))
    return [j * step for j in range(kmax + 1)]


def staircase_deltas(step: float, cutoff: float, rate: float) -> list[tuple[float, float]]:
    """Return `(theta, delta)` with cumulative weight dominating exp(rate*x).

    For theta_j = j*step, set the cumulative staircase through theta_j to
    exp(rate * min(theta_j + step, cutoff + step)).  If all samples satisfy
    x <= cutoff, this dominates exp(rate*x).
    """

    thetas = staircase_thresholds(step, cutoff)
    out: list[tuple[float, float]] = []
    prev = 0.0
    for theta in thetas:
        cap = min(theta + step, cutoff + step)
        cumulative = math.exp(rate * cap)
        out.append((theta, cumulative - prev))
        prev = cumulative
    return out


def empirical_budget(xs: list[float], step: float, cutoff: float, rate: float) -> float:
    deltas = staircase_deltas(step, cutoff, rate)
    total = 0.0
    for theta, delta in deltas:
        count = sum(1 for x in xs if theta <= x)
        total += delta * count
    return total / len(xs)


def envelope_budget(
    sample_size: int,
    step: float,
    cutoff: float,
    rate: float,
    c_bulk: float,
    spike_budget: float,
) -> float:
    deltas = staircase_deltas(step, cutoff, rate)
    total = 0.0
    for theta, delta in deltas:
        bound_per_sample = c_bulk * math.exp(-theta / 2) + spike_budget / sample_size
        total += delta * bound_per_sample
    return total


def direct_mgf(xs: list[float], rate: float) -> float:
    return sum(math.exp(rate * x) for x in xs) / len(xs)


def exact_cases(max_n: int, max_p: int) -> list[tuple[str, int, int, int, int, list[float]]]:
    anchors = [
        (32, 1153, "small-index"),
        (32, 32993, "spike"),
        (64, 16778497, "spike"),
        (128, 268437889, "control"),
        (256, 16778497, "r184-shared-prime"),
    ]
    out = []
    for n, p, label in anchors:
        if n <= max_n and p <= max_p and (p - 1) % n == 0:
            xs = list(normalized_values_vectorized(p, n, 32768))
            out.append((label, n, p, len(xs), p - 1, xs))
    return out


def prize_cases(ns: list[int], samples: int, seed: int, min_index_power: int) -> list[tuple[str, int, int, int, int, list[float]]]:
    min_index = 2**min_index_power
    out = []
    for offset, n in enumerate(ns):
        p, m = next_prime_congruent_one(n, min_index)
        xs = normalized_samples(p, n, samples, seed + offset)
        out.append((f"prize M_offset={m - min_index}", n, p, m, p - 1, xs))
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["exact", "prize"], default="prize")
    parser.add_argument("--ns", type=int, nargs="+", default=[64, 128, 256, 512])
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=466217)
    parser.add_argument("--min-index-power", type=int, default=128)
    parser.add_argument("--max-n", type=int, default=256)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--cutoff", type=float, default=32.0)
    parser.add_argument("--rate", type=float, default=0.25)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument(
        "--carrier",
        choices=["sample", "coset", "frequency"],
        default="coset",
        help="population size used for the closed envelope spike term",
    )
    args = parser.parse_args()

    if args.mode == "exact":
        cases = exact_cases(args.max_n, args.max_p)
    else:
        cases = prize_cases(args.ns, args.samples, args.seed, args.min_index_power)

    print(
        f"R217 normalized-square finite-grid budget mode={args.mode} "
        f"step={args.step} cutoff={args.cutoff} rate={args.rate} "
        f"C={args.c_bulk} K={args.spike_budget} carrier={args.carrier}"
    )
    print("n     sample   carrier      maxX    mgf      empirical  envelope   env_slack label")
    print("-" * 118)
    worst_env = (-1e100, None)
    worst_emp = (-1e100, None)
    for label, n, p, coset_pop, freq_pop, xs in cases:
        if args.carrier == "sample":
            envelope_population = len(xs)
        elif args.carrier == "coset":
            envelope_population = coset_pop
        else:
            envelope_population = freq_pop
        cutoff = max(args.cutoff, max(xs))
        emp = empirical_budget(xs, args.step, cutoff, args.rate)
        env = envelope_budget(
            envelope_population,
            args.step,
            cutoff,
            args.rate,
            args.c_bulk,
            args.spike_budget,
        )
        mgf = direct_mgf(xs, args.rate)
        env_slack = 2.0 - env
        if env > worst_env[0]:
            worst_env = (env, (n, p, label, cutoff))
        if emp > worst_emp[0]:
            worst_emp = (emp, (n, p, label, cutoff))
        print(
            f"{n:<5d} {len(xs):<8d} {envelope_population:<12d} {max(xs):<7.3f} {mgf:<8.4f} "
            f"{emp:<10.4f} {env:<10.4f} {env_slack:<9.4f} {label}"
        )

    print("\nsummary")
    print(f"tested={len(cases)}")
    if cases:
        env, (n, p, label, cutoff) = worst_env
        print(f"worst_envelope={env:.6f} slack={2-env:.6f} n={n} p={p} cutoff={cutoff:.3f} {label}")
        emp, (n, p, label, cutoff) = worst_emp
        print(f"worst_empirical={emp:.6f} slack={2-emp:.6f} n={n} p={p} cutoff={cutoff:.3f} {label}")


if __name__ == "__main__":
    main()
