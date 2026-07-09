#!/usr/bin/env python3
"""#466 R200: vectorized large-index grid sweep for the bulk-plus-two tail law.

R199 showed that exact vectorized coset-period evaluation makes million-coset
anchors tractable.  This probe turns that into a structured large-index sweep:

    p = M*n + 1 prime, n = 2^a, M >= 32,

with starts near n^2, n^3, n^4, and selected larger anchors.  It stress-tests
the R189/R197 large branch

    N(T) <= 0.6 * M * exp(-T/2) + 2

and records the direct quarter-MGF and spike ratio exp(max X / 4) / M.
"""

from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r186_mgf_quarter_stress import next_primes_congruent_one  # noqa: E402
from scripts.probes.probe_r199_vectorized_large_anchor_tail import (  # noqa: E402
    ANCHORS as R199_ANCHORS,
    normalized_values_vectorized,
    tail_stats,
)


def case_set(max_n: int, max_p: int, primes_per_start: int) -> set[tuple[int, int, str]]:
    out = {(n, p, f"r199:{label}") for n, p, label in R199_ANCHORS if n <= max_n and p <= max_p}
    n = 8
    while n <= max_n:
        starts = [max(257, n**2), n**3, n**4]
        if n >= 64:
            starts.append(2 * n**4)
        if n >= 128:
            starts.append(n**5)
        for start in starts:
            if start > max_p:
                continue
            for p in next_primes_congruent_one(n, start, primes_per_start):
                if p <= max_p:
                    out.add((n, p, f"grid-start={start}"))
        n *= 2
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunk", type=int, default=32768)
    parser.add_argument("--c-bulk", type=float, default=0.6)
    parser.add_argument("--spike-budget", type=float, default=2.0)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--min-index", type=int, default=32)
    parser.add_argument("--max-n", type=int, default=512)
    parser.add_argument("--max-p", type=int, default=350_000_000)
    parser.add_argument("--primes-per-start", type=int, default=2)
    parser.add_argument("--limit", type=int, default=0, help="optional cap after sorting cases")
    args = parser.parse_args()

    cases = sorted(case_set(args.max_n, args.max_p, args.primes_per_start))
    if args.limit:
        cases = cases[: args.limit]

    rows = []
    violations = []
    for n, p, label in cases:
        m = (p - 1) // n
        if m < args.min_index:
            continue
        xs = normalized_values_vectorized(p, n, args.chunk)
        excess, theta, max_x, mgf4, count = tail_stats(
            xs, args.c_bulk, args.spike_budget, args.step
        )
        ratio = math.exp(max_x / 4) / len(xs)
        rows.append((excess, mgf4, max_x, ratio, len(xs), n, p, theta, count, label))
        if excess > 1e-9:
            violations.append(rows[-1])

    rows.sort(reverse=True)
    violations.sort(reverse=True)
    print(
        f"R200 vectorized large-grid sweep: C={args.c_bulk} K={args.spike_budget} "
        f"min_index={args.min_index} chunk={args.chunk} tested={len(rows)} "
        f"violations={len(violations)}"
    )
    print("excess    mgf1/4  maxX    spike/M   M        n     p          T,count  label")
    print("-" * 112)
    for excess, mgf4, max_x, ratio, m, n, p, theta, count, label in rows[:40]:
        print(
            f"{excess:<9.3f} {mgf4:<7.4f} {max_x:<7.3f} {ratio:<9.6f} "
            f"{m:<8d} {n:<5d} {p:<10d} {theta:<4.1f},{count:<5d} {label}"
        )

    print("\nsummary")
    print(f"max_positive_excess={max([v[0] for v in violations], default=0.0):.6f}")
    if rows:
        worst_ratio = max(rows, key=lambda r: r[3])
        worst_mgf = max(rows, key=lambda r: r[1])
        print(
            "worst_spike_ratio="
            f"{worst_ratio[3]:.6f} n={worst_ratio[5]} p={worst_ratio[6]} M={worst_ratio[4]} "
            f"maxX={worst_ratio[2]:.6f} label={worst_ratio[9]}"
        )
        print(
            "worst_mgf="
            f"{worst_mgf[1]:.6f} n={worst_mgf[5]} p={worst_mgf[6]} M={worst_mgf[4]} "
            f"maxX={worst_mgf[2]:.6f} label={worst_mgf[9]}"
        )
    if violations:
        print("first violations")
        for excess, mgf4, max_x, ratio, m, n, p, theta, count, label in violations[:12]:
            print(
                f"  excess={excess:.6f} n={n} p={p} M={m} T={theta:.2f} "
                f"count={count} mgf1/4={mgf4:.6f} spike/M={ratio:.6f} {label}"
            )


if __name__ == "__main__":
    main()
