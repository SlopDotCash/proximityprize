#!/usr/bin/env python3
"""#466 R189: bulk-plus-spikes tail certificate for MGF(1/4) <= 2.

R186 made MGF(1/4) <= 2 the clean tower residual.  This probe tests a
stronger structural route:

    N(T) <= C * M * exp(-T/2) + K.

The first term is a Gaussian/exponential bulk envelope; the additive one
absorbs the rare coherent spikes that defeat a pure exp(-T/2) tail in the
R63 adversarial rows.  We also compute the exact half-grid layer-cake budget
induced by that envelope for exp(X/4).
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r186_mgf_quarter_stress import (  # noqa: E402
    next_primes_congruent_one,
    normalized_values,
)


def case_set(include_huge: bool) -> set[tuple[int, int, str]]:
    cases: set[tuple[int, int, str]] = {
        (32, 32993, "r63-spike"),
        (64, 16778497, "r63-spike"),
        (128, 2101249, "r63-small-spike"),
        (128, 268437889, "r63-control"),
        (256, 16777729, "r172-control"),
        (512, 262657, "r172-high"),
    }
    for n in (8, 16, 32, 64, 128, 256):
        count = 6 if n <= 64 else 3
        for start in (max(257, n**2), n**3, n**4):
            for p in next_primes_congruent_one(n, start, count):
                if include_huge or p <= 30_000_000:
                    cases.add((n, p, f"grid-start={start}"))
    return cases


def mgf(xs: list[float], rate: float) -> float:
    return sum(math.exp(rate * x) for x in xs) / len(xs)


def survival_count(xs: list[float], threshold: float) -> int:
    return sum(1 for x in xs if threshold <= x)


def layercake_budget(xs: list[float], c_bulk: float, spike_budget: float, step: float) -> tuple[float, float]:
    """Return envelope budget per point and the largest tested threshold.

    For grid θ_j = j*step, use
      exp(x/4) <= exp(step/4) + sum_{θ_j <= x, j>=2}
        (exp(θ_j/4) - exp((θ_j-step)/4)).
    The count at θ_j is bounded by c_bulk*M*exp(-θ_j/2)+spike_budget.
    """
    max_x = max(xs)
    m = len(xs)
    base = math.exp(step / 4)
    total = base * m
    j = 2
    while j * step <= max_x + 1e-12:
        theta = j * step
        delta = math.exp(theta / 4) - math.exp((theta - step) / 4)
        total += delta * (c_bulk * m * math.exp(-theta / 2) + spike_budget)
        j += 1
    return total / m, (j - 1) * step


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c-bulk", type=float, default=0.60)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--include-huge", action="store_true")
    args = parser.parse_args()

    rows = []
    violations = []
    for n, p, label in sorted(case_set(args.include_huge)):
        xs = normalized_values(p, n)
        m = len(xs)
        max_x = max(xs)
        worst_excess = -10**9
        worst_theta = 0.0
        worst_count = 0
        j = 2
        while j * args.step <= max_x + 1e-12:
            theta = j * args.step
            count = survival_count(xs, theta)
            bound = args.c_bulk * m * math.exp(-theta / 2) + args.spike_budget
            excess = count - bound
            if excess > worst_excess:
                worst_excess = excess
                worst_theta = theta
                worst_count = count
            if excess > 1e-9:
                violations.append((excess, n, p, label, theta, count, bound))
            j += 1
        budget, max_grid = layercake_budget(xs, args.c_bulk, args.spike_budget, args.step)
        rows.append((budget, mgf(xs, 1 / 4), n, p, label, m, max_x, worst_excess, worst_theta, worst_count, max_grid))

    rows.sort(reverse=True)
    print(
        f"bulk-plus-spikes envelope: N(T) <= "
        f"{args.c_bulk} M exp(-T/2) + {args.spike_budget}"
    )
    print(f"grid step={args.step} tested_cases={len(rows)} violations={len(violations)}")
    print()
    print("worst layer-cake budgets")
    print("budget  mgf1/4  n    p          cosets    maxX    excess@T,count  label")
    print("-" * 104)
    for budget, m4, n, p, label, cosets, max_x, excess, theta, count, _ in rows[:25]:
        print(
            f"{budget:<7.4f} {m4:<7.4f} {n:<4d} {p:<10d} {cosets:<9d} "
            f"{max_x:<7.3f} {excess:>8.3f}@{theta:<4.1f},{count:<5d} {label}"
        )

    print("\nsummary")
    print(f"worst_budget={rows[0][0]:.6f} n={rows[0][2]} p={rows[0][3]} label={rows[0][4]}")
    print(f"worst_mgf1/4={max(rows, key=lambda r: r[1])[1]:.6f}")
    print(f"max_positive_excess={max([v[0] for v in violations], default=0.0):.6f}")
    if violations:
        print("first violations")
        for excess, n, p, label, theta, count, bound in sorted(violations, reverse=True)[:10]:
            print(
                f"  excess={excess:.6f} n={n} p={p} T={theta:.2f} "
                f"count={count} bound={bound:.6f} {label}"
            )


if __name__ == "__main__":
    main()
