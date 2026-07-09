#!/usr/bin/env python3
"""#466 R178: dyadic tower splitting of Gaussian-period spectra.

The compensation law may come from the tower μ_n ⊂ μ_{2n}: a parent coset
period for μ_{2n} is a sum of two child periods for μ_n.  This probe measures
how normalized squared magnitudes split between levels at the same prime.
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


def subgroup_step(p: int, order: int) -> int:
    return pow(primitive_root(p), (p - 1) // order, p)


def period_by_coset_index(p: int, order: int) -> list[complex]:
    """Return periods for cosets of μ_order indexed by primitive-root exponent."""
    g = primitive_root(p)
    step = pow(g, (p - 1) // order, p)
    zeta = cmath.exp(2j * math.pi / p)
    vals = []
    reps = (p - 1) // order
    for j in range(reps):
        b = pow(g, j, p)
        x = 1
        s = 0j
        for _ in range(order):
            s += zeta ** ((b * x) % p)
            x = (x * step) % p
        vals.append(s)
    return vals


def normalized_mags2(vals: list[complex]) -> list[float]:
    mags = [z.real * z.real + z.imag * z.imag for z in vals]
    mean = sum(mags) / len(mags)
    return [m / mean for m in mags]


def split_stats(p: int, n: int) -> dict[str, float]:
    child = period_by_coset_index(p, n)
    parent = period_by_coset_index(p, 2 * n)
    child_x = normalized_mags2(child)
    parent_x = normalized_mags2(parent)
    # μ_n cosets refine μ_{2n} cosets: parent index j contains child indices j and j+k,
    # where k=(p-1)/(2n), because μ_{2n}=μ_n ∪ g^k μ_n.
    k = (p - 1) // (2 * n)
    ratios = []
    cancellations = []
    polar = []
    for j, par in enumerate(parent):
        a = child[j]
        b = child[j + k]
        denom = (abs(a) + abs(b)) ** 2
        cancellations.append((abs(par) ** 2) / denom if denom else 0.0)
        sx = child_x[j] + child_x[j + k]
        px = parent_x[j]
        ratios.append(px / sx if sx else 0.0)
        polar.append(abs(child_x[j] - child_x[j + k]) / (sx if sx else 1.0))

    return {
        "child_s1": sum(1 for x in child_x if x >= 1) / len(child_x),
        "parent_s1": sum(1 for x in parent_x if x >= 1) / len(parent_x),
        "child_low": sum(1 for x in child_x if x < 0.5) / len(child_x),
        "parent_low": sum(1 for x in parent_x if x < 0.5) / len(parent_x),
        "child_s4": sum(1 for x in child_x if x >= 4) / len(child_x),
        "parent_s4": sum(1 for x in parent_x if x >= 4) / len(parent_x),
        "ratio_mean": sum(ratios) / len(ratios),
        "ratio_min": min(ratios),
        "ratio_max": max(ratios),
        "cancel_mean": sum(cancellations) / len(cancellations),
        "cancel_min": min(cancellations),
        "polar_mean": sum(polar) / len(polar),
    }


def main() -> None:
    cases = []
    for n in (16, 32, 64, 128):
        p = first_prime_congruent_one(2 * n, max((2 * n) ** 4, 100_000))
        if p < 300_000_000:
            cases.append((p, n))
    print("p          n->2n   childS1 parentS1 childLow parentLow childS4 parentS4 splitRatio[min,mean,max] cancel[min,mean] polar")
    print("-" * 132)
    for p, n in cases:
        st = split_stats(p, n)
        print(
            f"{p:<10d} {n:<3d}->{2*n:<3d} "
            f"{st['child_s1']:<7.3f} {st['parent_s1']:<8.3f} "
            f"{st['child_low']:<8.3f} {st['parent_low']:<9.3f} "
            f"{st['child_s4']:<7.3f} {st['parent_s4']:<8.3f} "
            f"[{st['ratio_min']:.3f},{st['ratio_mean']:.3f},{st['ratio_max']:.3f}] "
            f"[{st['cancel_min']:.3f},{st['cancel_mean']:.3f}] {st['polar_mean']:.3f}"
        )


if __name__ == "__main__":
    main()
