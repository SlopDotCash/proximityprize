#!/usr/bin/env python3
"""#466 R191: stress-test the dyadic tower product-MGF fixed point.

R190 found that the R168 paired product budget

  avg_i exp(left_i/8) exp(right_i/8)

is about 4/3, far below the Lean consumer's sufficient bound 2.  For independent
real Gaussians, left and right normalized squares are chi^2_1, so the target is

  E exp((X+Y)/8) = (1 - 2*(1/8))^-1 = 4/3.

This probe stresses that fixed point across primes and dyadic levels and also
checks nearby rates.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402


def normalized(vals: list[complex]) -> list[float]:
    sigma = sum(abs(z) ** 2 for z in vals) / len(vals)
    return [abs(z) ** 2 / sigma for z in vals]


def product_mgf(p: int, n: int, rate: float) -> float:
    child = period_by_coset_index(p, n // 2)
    cx = normalized(child)
    step = (p - 1) // n
    return sum(math.exp(rate * (cx[j] + cx[j + step])) for j in range((p - 1) // n)) / ((p - 1) // n)


def parent_mgf(p: int, n: int, rate: float) -> float:
    parent = period_by_coset_index(p, n)
    px = normalized(parent)
    return sum(math.exp(rate * x) for x in px) / len(px)


def main() -> None:
    cases = [
        (16, 1048609),
        (16, 1048897),
        (16, 1049057),
        (16, 1049089),
        (16, 1049281),
        (32, 16777601),
        (32, 16777729),
        (32, 16778497),
        (32, 16778561),
        (32, 16778689),
        (64, 16778497),
        (128, 268437889),
        (256, 16777729),
    ]
    rates = [1 / 16, 1 / 8, 1 / 6, 1 / 4]
    targets = {r: (1 - 2 * r) ** -1 if r < 0.5 else float("inf") for r in rates}
    print("independent chi-square product targets:")
    for r in rates:
        print(f"  rate={r:.6f} target={targets[r]:.6g}")
    print()
    print("n p prod1/16 prod1/8 prod1/6 prod1/4 parent1/8 ratio_to_4/3")
    for n, p in cases:
        vals = [product_mgf(p, n, r) for r in rates]
        pm = parent_mgf(p, n, 1 / 8)
        print(
            f"{n:<3d} {p:<10d} "
            f"{vals[0]:.6f} {vals[1]:.6f} {vals[2]:.6f} {vals[3]:.6g} "
            f"{pm:.6f} {vals[1] / (4 / 3):.6f}"
        )


if __name__ == "__main__":
    main()
