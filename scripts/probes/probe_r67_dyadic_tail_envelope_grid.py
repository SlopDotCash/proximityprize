#!/usr/bin/env python3
"""#466 R67: broad falsification grid for dyadic tail envelope.

R66 found large slack for N(T) <= M exp(-T/4) on selected dyadic spike/control
cases.  This probe scans many admissible primes and lower thresholds to try to
break that envelope.
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


THRESHOLDS = [1.1, 1.25, 1.5, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 28, 32]


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


def worst_ratio(xs: list[float], alpha: float) -> tuple[float, float, int]:
    m = len(xs)
    best = (0.0, 0.0, 0)
    for t in THRESHOLDS:
        count = sum(1 for x in xs if x >= t)
        ratio = count / (m * math.exp(-alpha * t))
        if ratio > best[0]:
            best = (ratio, t, count)
    return best


def main() -> None:
    rows = []
    for n in (8, 16, 32, 64, 128):
        starts = [max(257, n**2), n**3, n**4]
        count = 10 if n <= 64 else 4
        for start in starts:
            for p in next_primes_congruent_one(n, start, count):
                if p > 350_000_000:
                    continue
                xs = normalized_values(p, n)
                r25 = worst_ratio(xs, 0.25)
                r33 = worst_ratio(xs, 1 / 3)
                rows.append((r25[0], r25[1], r25[2], r33[0], n, p, len(xs), max(xs)))

    rows.sort(reverse=True)
    print("worst rows for N(T) <= M exp(-T/4)")
    print("ratio   T     count   n    p          cosets    maxX    ratio_exp(-T/3)")
    print("-" * 86)
    for ratio, t, count, ratio33, n, p, m, max_x in rows[:25]:
        print(f"{ratio:<7.4f} {t:<5g} {count:<7d} {n:<4d} {p:<10d} {m:<9d} {max_x:<7.3f} {ratio33:.4f}")

    violations = [r for r in rows if r[0] > 1 + 1e-9]
    print("\nsummary")
    print(f"tested={len(rows)} violations_exp(-T/4)={len(violations)}")
    if violations:
        ratio, t, count, ratio33, n, p, m, max_x = violations[0]
        print(f"worst violation n={n} p={p} T={t} count={count} ratio={ratio:.6g} maxX={max_x:.6g}")


if __name__ == "__main__":
    main()
