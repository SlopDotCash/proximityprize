#!/usr/bin/env python3
"""R326: test the coarse/fine half-CS inequality for dyadic period children."""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import first_prime_congruent_one


def row(n: int) -> tuple[float | int, ...]:
    p = first_prime_congruent_one(2 * n, max((2 * n) ** 4, 100_000))
    child = period_by_coset_index(p, n)
    pairs = (p - 1) // (2 * n)
    ab = [(child[j].real, child[j + pairs].real) for j in range(pairs)]
    a4 = sum(a**4 + b**4 for a, b in ab)
    cross = sum(2 * a * a * b * b for a, b in ab)
    odd = sum(4 * (a**3 * b + a * b**3) for a, b in ab)
    u4 = a4 + 3 * cross + odd
    v4 = a4 + 3 * cross - odd
    mixed = a4 - cross
    kappa = mixed / math.sqrt(u4 * v4)
    rhs = (5 * cross - a4) * (3 * a4 + cross)
    return n, p, pairs, kappa, a4 / cross, odd / (a4 + 3 * cross), rhs - odd * odd


def main() -> None:
    print("n p pairs kappa A4/C O/(A4+3C) certificate_slack")
    for n in (8, 16, 32, 64):
        values = row(n)
        print(
            f"{values[0]} {values[1]} {values[2]} {values[3]:.12f} "
            f"{values[4]:.12f} {values[5]:.12e} {values[6]:.12e}"
        )


if __name__ == "__main__":
    main()
