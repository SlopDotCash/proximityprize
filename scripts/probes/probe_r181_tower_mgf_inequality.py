#!/usr/bin/env python3
"""#466 R181: candidate inequalities for the dyadic tower MGF step.

For μ_n ⊂ μ_{2n}, each parent period is a+b from two child periods.  This
probe compares the actual parent exp(|a+b|^2/(8σ_parent^2)) average with
deterministic upper envelopes computed from child magnitudes.
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    first_prime_congruent_one,
    primitive_root,
)


def periods(p: int, order: int) -> list[complex]:
    g = primitive_root(p)
    step = pow(g, (p - 1) // order, p)
    zeta = cmath.exp(2j * math.pi / p)
    vals = []
    for j in range((p - 1) // order):
        b = pow(g, j, p)
        x = 1
        s = 0j
        for _ in range(order):
            s += zeta ** ((b * x) % p)
            x = (x * step) % p
        vals.append(s)
    return vals


def mean_sq(vals: list[complex]) -> float:
    return sum(abs(z) ** 2 for z in vals) / len(vals)


def tower_bounds(p: int, n: int) -> dict[str, float]:
    child = periods(p, n)
    parent = periods(p, 2 * n)
    sigma_child = mean_sq(child)
    sigma_parent = mean_sq(parent)
    k = (p - 1) // (2 * n)
    actual = []
    tri = []
    avg_energy = []
    child_mean = []
    phase = []
    for j, z in enumerate(parent):
        a = child[j]
        b = child[j + k]
        x = abs(a) ** 2 / sigma_child
        y = abs(b) ** 2 / sigma_child
        actual.append(math.exp((abs(z) ** 2 / sigma_parent) / 8))
        # |a+b|^2 <= (|a|+|b|)^2.
        tri.append(math.exp((((abs(a) + abs(b)) ** 2) / sigma_parent) / 8))
        # |a+b|^2 <= 2(|a|^2+|b|^2).
        avg_energy.append(math.exp((2 * (abs(a) ** 2 + abs(b) ** 2) / sigma_parent) / 8))
        # Jensen-ish child average candidate.
        child_mean.append(0.5 * (math.exp(x / 8) + math.exp(y / 8)))
        # Actual phase factor times child energy sum.
        denom = (abs(a) + abs(b)) ** 2
        c = (abs(z) ** 2 / denom) if denom else 0.0
        phase.append(math.exp((c * (abs(a) + abs(b)) ** 2 / sigma_parent) / 8))
    return {
        "actual": sum(actual) / len(actual),
        "tri": sum(tri) / len(tri),
        "avg_energy": sum(avg_energy) / len(avg_energy),
        "child_mean": sum(child_mean) / len(child_mean),
        "phase": sum(phase) / len(phase),
        "sigma_ratio": sigma_parent / sigma_child,
    }


def main() -> None:
    p = first_prime_congruent_one(512, 512**2)
    print(f"p={p}")
    print("n->2n actual   childAvg tri      energy   phase    sigma_parent/child")
    print("-" * 84)
    for n in (16, 32, 64, 128, 256):
        b = tower_bounds(p, n)
        print(
            f"{n:<3d}->{2*n:<3d} {b['actual']:<8.5f} {b['child_mean']:<8.5f} "
            f"{b['tri']:<8.5f} {b['avg_energy']:<8.5f} {b['phase']:<8.5f} {b['sigma_ratio']:.5f}"
        )


if __name__ == "__main__":
    main()
