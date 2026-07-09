#!/usr/bin/env python3
"""#466 R228: stress the natural quotient-tail envelope from R227.

R227 packages the prize endpoint around the natural quotient law

    #{quotient cosets with X >= T} <= 0.6 * M * exp(-T/2) + 2,

where M = (p - 1) / n and X is the normalized squared Gauss-period value on
one representative per μ_n-coset.  This probe broadens R220 from a few anchors
to a mixed medium/large sweep and records the worst quotient excess.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

import numpy as np  # noqa: E402

from scripts.probes.probe_r226_half_band_quotient_tail_sweep import (  # noqa: E402
    is_prime,
    normalized_values_vectorized,
)
from scripts.probes.probe_r220_raw_vs_quotient_spike_budget import (  # noqa: E402
    DEFAULT_ROWS as R220_ROWS,
)


def case_set(max_n: int, max_p: int, primes_per_start: int) -> set[tuple[int, int, str]]:
    """Small local replacement for the untracked R200 large-grid case helper."""
    out: set[tuple[int, int, str]] = set()
    starts = (2**16, 2**20, 2**24, 2**28)
    n = 16
    while n <= max_n:
        for start in starts:
            if start > max_p:
                continue
            p = start + ((1 - start) % n)
            found = 0
            while p <= max_p and found < primes_per_start:
                if is_prime(p):
                    out.add((n, p, f"large-start={start}"))
                    found += 1
                p += n
        n *= 2
    return out


def medium_cases(max_a: int, max_index: int) -> set[tuple[int, int, str]]:
    out: set[tuple[int, int, str]] = set()
    for a in range(3, max_a + 1):
        n = 2**a
        for m in range(2, max_index + 1):
            p = m * n + 1
            if is_prime(p):
                out.add((n, p, f"medium-a={a}-M={m}"))
    return out


def tail_excess(
    xs: np.ndarray, c_bulk: float, spike_budget: float, step: float, min_theta: float
) -> tuple[float, float, int]:
    max_x = float(xs.max())
    worst_excess = -1.0e100
    worst_theta = 0.0
    worst_count = 0
    j = max(1, math.ceil(min_theta / step))
    while j * step <= max_x + 1.0e-12:
        theta = j * step
        count = int(np.count_nonzero(xs >= theta))
        bound = c_bulk * len(xs) * math.exp(-theta / 2) + spike_budget
        excess = count - bound
        if excess > worst_excess:
            worst_excess = excess
            worst_theta = theta
            worst_count = count
        j += 1
    return worst_excess, worst_theta, worst_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.25)
    parser.add_argument("--min-theta", type=float, default=1.0)
    parser.add_argument("--medium-max-a", type=int, default=11)
    parser.add_argument("--medium-max-index", type=int, default=512)
    parser.add_argument("--min-index", type=int, default=1)
    parser.add_argument("--large-max-n", type=int, default=512)
    parser.add_argument("--large-max-p", type=int, default=350_000_000)
    parser.add_argument("--large-primes-per-start", type=int, default=1)
    parser.add_argument("--skip-large", action="store_true")
    parser.add_argument("--top", type=int, default=40)
    args = parser.parse_args()

    cases = {(n, p, f"r220:{label}") for n, p, label in R220_ROWS}
    cases |= medium_cases(args.medium_max_a, args.medium_max_index)
    if args.skip_large:
        cases = {(n, p, label) for n, p, label in cases if p <= 20_000_000}
    else:
        cases |= case_set(args.large_max_n, args.large_max_p, args.large_primes_per_start)

    rows = []
    for n, p, label in sorted(cases):
        if (p - 1) // n < args.min_index:
            continue
        xs = normalized_values_vectorized(p, n, args.chunk)
        excess, theta, count = tail_excess(
            xs, args.c_bulk, args.spike_budget, args.step, args.min_theta
        )
        max_x = float(xs.max())
        mgf4 = float(np.exp(xs / 4).mean())
        ratio = math.exp(max_x / 4) / len(xs)
        rows.append((excess, theta, count, max_x, mgf4, ratio, len(xs), n, p, label))

    rows.sort(reverse=True)
    violations = [row for row in rows if row[0] > 1e-9]
    print(
        f"R228 natural quotient-tail sweep: C={args.c_bulk} K={args.spike_budget} "
        f"step={args.step} min_theta={args.min_theta} min_index={args.min_index} "
        f"tested={len(rows)} violations={len(violations)}"
    )
    print("excess    T,count  maxX    mgf1/4  spike/M   M        n     p          label")
    print("-" * 116)
    for excess, theta, count, max_x, mgf4, ratio, m, n, p, label in rows[: args.top]:
        print(
            f"{excess:<9.3f} {theta:<5.2f},{count:<5d} {max_x:<7.3f} {mgf4:<7.4f} "
            f"{ratio:<9.6f} {m:<8d} {n:<5d} {p:<10d} {label}"
        )

    print("\nsummary")
    print(f"max_excess={max([row[0] for row in rows], default=0.0):.6f}")
    print(f"positive_count={len(violations)}")
    if rows:
        worst_mgf = max(rows, key=lambda row: row[4])
        worst_spike = max(rows, key=lambda row: row[5])
        print(
            "worst_mgf="
            f"{worst_mgf[4]:.6f} n={worst_mgf[7]} p={worst_mgf[8]} M={worst_mgf[6]} "
            f"maxX={worst_mgf[3]:.6f} label={worst_mgf[9]}"
        )
        print(
            "worst_spike_ratio="
            f"{worst_spike[5]:.6f} n={worst_spike[7]} p={worst_spike[8]} M={worst_spike[6]} "
            f"maxX={worst_spike[3]:.6f} label={worst_spike[9]}"
        )


if __name__ == "__main__":
    main()
