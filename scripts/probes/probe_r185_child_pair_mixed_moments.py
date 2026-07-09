#!/usr/bin/env python3
"""#466 R185: mixed moments of dyadic tower child-period pairs.

R183/R184 show angle equidistribution for child pairs in μ_n ⊂ μ_2n.
This probe tests the more algebraic fixed-point statement: the two child
periods behave like independent real Gaussians after RMS normalization.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2]))

from scripts.probes.probe_r178_dyadic_tower_split import period_by_coset_index  # noqa: E402
from scripts.probes.probe_r59_large_moment_ratio_monotonicity import (  # noqa: E402
    first_prime_congruent_one,
)


MOMENTS = [(1, 1), (2, 2), (4, 0), (4, 2), (4, 4), (6, 0)]
GAUSSIAN = {
    (1, 1): 0.0,
    (2, 2): 1.0,
    (4, 0): 3.0,
    (4, 2): 3.0,
    (4, 4): 9.0,
    (6, 0): 15.0,
}


def mixed_moments(p: int, n: int) -> dict[tuple[int, int], float]:
    child = period_by_coset_index(p, n)
    k = (p - 1) // (2 * n)
    pairs = [(child[j].real, child[j + k].real) for j in range((p - 1) // (2 * n))]
    va = sum(a * a for a, _ in pairs) / len(pairs)
    vb = sum(b * b for _, b in pairs) / len(pairs)
    sa = math.sqrt(va)
    sb = math.sqrt(vb)
    return {
        (u, v): sum((a / sa) ** u * (b / sb) ** v for a, b in pairs) / len(pairs)
        for (u, v) in MOMENTS
    }


def main() -> None:
    print("Gaussian targets:", " ".join(f"{k}:{v:g}" for k, v in GAUSSIAN.items()))
    print("p          n->2n   pairs    " + " ".join(f"m{u}{v}" for u, v in MOMENTS))
    print("-" * 104)
    for n in (16, 32, 64):
        p = first_prime_congruent_one(2 * n, max((2 * n) ** 4, 100_000))
        m = mixed_moments(p, n)
        print(
            f"{p:<10d} {n:<3d}->{2*n:<3d} {(p-1)//(2*n):<8d} "
            + " ".join(f"{m[key]:<8.5f}" for key in MOMENTS)
        )


if __name__ == "__main__":
    main()
