#!/usr/bin/env python3
"""#466 R198: stress the large-index bulk-plus-two tail law.

R197 split the quarter-MGF route into finite small-index certificates and a
large-index tail theorem.  This probe stress-tests the large branch:

    N(T) <= C * M * exp(-T/2) + K

on a wider dyadic case set, filtering by M=(p-1)/n >= min-index.
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


ANCHORS: tuple[tuple[int, int, str], ...] = (
    (32, 32993, "r63-spike"),
    (64, 16778497, "r63-spike"),
    (128, 2101249, "r63-small-spike"),
    (128, 268437889, "r63-control"),
    (256, 16777729, "r172-control"),
    (512, 262657, "r172-high"),
)


def cases(max_n: int, primes_per_start: int, max_p: int) -> set[tuple[int, int, str]]:
    out = {(n, p, label) for n, p, label in ANCHORS if p <= max_p and n <= max_n}
    n = 8
    while n <= max_n:
        starts = [max(257, n**2), n**3, n**4]
        if n >= 64:
            starts.append(2 * n**4)
        for start in starts:
            for p in next_primes_congruent_one(n, start, primes_per_start):
                if p <= max_p:
                    out.add((n, p, f"grid-start={start}"))
        n *= 2
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--min-index", type=int, default=32)
    parser.add_argument("--max-n", type=int, default=1024)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--primes-per-start", type=int, default=3)
    args = parser.parse_args()

    rows = []
    violations = []
    for n, p, label in sorted(cases(args.max_n, args.primes_per_start, args.max_p)):
        m = (p - 1) // n
        if m < args.min_index:
            continue
        xs = normalized_values(p, n)
        max_x = max(xs)
        worst_excess = -10**18
        worst_theta = 0.0
        worst_count = 0
        j = 2
        while j * args.step <= max_x + 1e-12:
            theta = j * args.step
            count = sum(1 for x in xs if theta <= x)
            bound = args.c_bulk * len(xs) * math.exp(-theta / 2) + args.spike_budget
            excess = count - bound
            if excess > worst_excess:
                worst_excess = excess
                worst_theta = theta
                worst_count = count
            if excess > 1e-9:
                violations.append((excess, n, p, label, len(xs), theta, count, bound, max_x))
            j += 1
        mgf4 = sum(math.exp(x / 4) for x in xs) / len(xs)
        rows.append((worst_excess, mgf4, max_x, len(xs), n, p, label, worst_theta, worst_count))

    rows.sort(reverse=True)
    violations.sort(reverse=True)
    print(
        f"R198 large-index tail stress: C={args.c_bulk} K={args.spike_budget} "
        f"min_index={args.min_index} tested={len(rows)} violations={len(violations)}"
    )
    print("excess    mgf1/4  maxX    M        n     p          T,count  label")
    print("-" * 96)
    for excess, mgf4, max_x, m, n, p, label, theta, count in rows[:30]:
        print(
            f"{excess:<9.3f} {mgf4:<7.4f} {max_x:<7.3f} {m:<8d} "
            f"{n:<5d} {p:<10d} {theta:<4.1f},{count:<5d} {label}"
        )
    print("\nsummary")
    print(f"max_positive_excess={max([v[0] for v in violations], default=0.0):.6f}")
    if violations:
        print("first violations")
        for excess, n, p, label, m, theta, count, bound, max_x in violations[:12]:
            print(
                f"  excess={excess:.6f} n={n} p={p} M={m} T={theta:.2f} "
                f"count={count} bound={bound:.6f} maxX={max_x:.3f} {label}"
            )


if __name__ == "__main__":
    main()
