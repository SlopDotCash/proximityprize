#!/usr/bin/env python3
"""Falsify phase-blind exterior-power bounds for the injective D7 transform.

For weights ``w_j = exp(2*pi*i*j/p)``, ``0 <= j < n``, all weights are distinct p-th roots.
Nevertheless they occupy an arc of length ``2*pi*(n-1)/p``.  The ordered without-replacement
transform is

    D7 = 7! * e7(w_0,...,w_{n-1}).

Every seven-fold product lies in an arc ending before ``2*pi*7*(n-1)/p``.  When that angle is
below pi, averaging real parts gives the rigorous lower bound

    |D7| / (n)_7 >= cos(2*pi*7*(n-1)/p).

Thus the normalized transform tends to one as p/n tends to infinity.  Distinctness, unit modulus,
sampling without replacement, Maclaurin language, or an exterior-power reformulation alone cannot
give any universal saving.  Subgroup/additive structure is load-bearing.
"""

from __future__ import annotations

import cmath
import itertools
import math


DEPTH = 7


def elementary_symmetric(weights: list[complex], depth: int = DEPTH) -> complex:
    """Compute e_depth by the standard descending dynamic program."""
    e = [0j] * (depth + 1)
    e[0] = 1 + 0j
    for weight in weights:
        for k in range(depth, 0, -1):
            e[k] += weight * e[k - 1]
    return e[depth]


def brute_elementary_symmetric(weights: list[complex], depth: int = DEPTH) -> complex:
    return sum(
        (
            math.prod(weights[j] for j in indices)
            for indices in itertools.combinations(range(len(weights)), depth)
        ),
        0j,
    )


def falling_factorial(n: int, depth: int = DEPTH) -> int:
    return math.prod(range(n - depth + 1, n + 1))


def cluster_record(n: int, p: int) -> tuple[float, float]:
    assert p > n
    weights = [cmath.exp(2j * math.pi * j / p) for j in range(n)]
    transform = math.factorial(DEPTH) * elementary_symmetric(weights)
    ratio = abs(transform) / falling_factorial(n)
    terminal_angle = 2 * math.pi * DEPTH * (n - 1) / p
    assert terminal_angle < math.pi
    certified_lower = math.cos(terminal_angle)
    # Floating evaluation of the exact analytic inequality; tolerance covers roundoff only.
    assert ratio + 2e-12 >= certified_lower
    return ratio, certified_lower


def main() -> None:
    # Independent DP/brute-force consistency check.
    check_weights = [cmath.exp(2j * math.pi * j / 101) for j in range(10)]
    dp = elementary_symmetric(check_weights)
    brute = brute_elementary_symmetric(check_weights)
    assert abs(dp - brute) < 1e-10

    n = 64
    print("INJECTIVE_D7_DISTINCT_ROOT_CLUSTER")
    print(f"n={n} depth={DEPTH} normalization=(n)_7={falling_factorial(n)}")
    for p in (65537, 1_000_003, 1_000_000_007):
        ratio, lower = cluster_record(n, p)
        print(
            f"p={p} normalized_abs_D7={ratio:.15f} "
            f"analytic_cos_lower={lower:.15f}"
        )
    print(
        "VERDICT=no universal c<1 bound follows from distinct unit phases or "
        "sampling-without-replacement; subgroup mixing is essential"
    )


if __name__ == "__main__":
    main()
