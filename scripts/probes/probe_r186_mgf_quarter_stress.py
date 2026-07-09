#!/usr/bin/env python3
"""#466 R186: stress the dyadic MGF(1/4) <= 2 residual.

R185 shows that MGF(1/4) <= 2 on child halves is enough for the AM-GM tower
route to land the R168 parent MGF.  This probe stress-tests that higher-rate
MGF directly on exact dyadic spectra.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    coset_mags2,
    is_prime,
    subgroup,
)


def next_primes_congruent_one(n: int, start: int, count: int) -> list[int]:
    p = start + ((1 - start) % n)
    out = []
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


def normalized_values(p: int, n: int) -> list[float]:
    mags = coset_mags2(p, subgroup(p, n))
    sigma2 = n * sum(mags) / (p - 1)
    return [m / sigma2 for m in mags]


def mgf(xs: list[float], rate: float) -> float:
    return sum(math.exp(rate * x) for x in xs) / len(xs)


def main() -> None:
    cases: set[tuple[int, int, str]] = {
        (32, 32993, "r63-spike"),
        (64, 16778497, "r63-spike"),
        (128, 2101249, "r63-small-spike"),
        (128, 268437889, "r63-control"),
        (256, 16777729, "r172-control"),
        (512, 262657, "r172-high"),
    }
    for n in (8, 16, 32, 64, 128, 256):
        count = 8 if n <= 64 else 4
        for start in (max(257, n**2), n**3, n**4):
            for p in next_primes_congruent_one(n, start, count):
                if p <= 350_000_000:
                    cases.add((n, p, f"grid-start={start}"))

    rows = []
    for n, p, label in sorted(cases):
        xs = normalized_values(p, n)
        vals = {r: mgf(xs, r) for r in (1 / 8, 1 / 6, 1 / 4, 1 / 3)}
        rows.append((vals[1 / 4], vals[1 / 3], n, p, label, len(xs), max(xs), vals))
    rows.sort(reverse=True)

    print("worst rows by MGF(1/4)")
    print("mgf1/4  mgf1/3  n    p          cosets    maxX    label")
    print("-" * 86)
    for m4, m3, n, p, label, cosets, max_x, vals in rows[:25]:
        print(f"{m4:<7.4f} {m3:<7.4f} {n:<4d} {p:<10d} {cosets:<9d} {max_x:<7.3f} {label}")

    print("\nsummary")
    print(f"tested={len(rows)} violations_mgf1/4_le_2={sum(1 for r in rows if r[0] > 2 + 1e-9)}")
    print(f"worst_mgf1/4={rows[0][0]:.6f} n={rows[0][2]} p={rows[0][3]} label={rows[0][4]}")
    print(f"worst_mgf1/3={max(rows, key=lambda r: r[1])[1]:.6f}")


if __name__ == "__main__":
    main()
