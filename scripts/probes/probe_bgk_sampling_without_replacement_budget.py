#!/usr/bin/env python3
"""Exact production audit for the depth-seven without-replacement coupling.

The universal coupling

    |D7 - eta^7| <= n^7 - (n)_7

is sharp for aligned unit phases.  This probe uses integer arithmetic only to measure its gap from
the coefficient-126871 average per-frequency energy scale.  It also computes the best integer
period ceiling obtained by combining that coupling with the hypothetical pointwise square bound
``|D7|^2 <= 126871*n^7``.
"""

from __future__ import annotations

import math


DEPTH = 7
N = 2**30
COEFFICIENT = 126_871


def falling_factorial(n: int, r: int) -> int:
    return math.prod(range(n - r + 1, n + 1))


def ceil_sqrt(x: int) -> int:
    y = math.isqrt(x)
    return y if y * y == x else y + 1


def ceil_nth_root(x: int, r: int) -> int:
    lo, hi = 0, 1
    while hi**r < x:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**r >= x:
            hi = mid
        else:
            lo = mid
    return hi


def main() -> None:
    injective_count = falling_factorial(N, DEPTH)
    sampling_error = N**DEPTH - injective_count
    energy_budget = COEFFICIENT * N**DEPTH
    amplitude_ceiling = ceil_sqrt(energy_budget)
    period_ceiling = ceil_nth_root(sampling_error + amplitude_ceiling, DEPTH)
    paley_ceiling = ceil_sqrt(2 * N)

    assert 2**184 < sampling_error < 2**185
    assert 2**226 < energy_budget < 2**227
    assert 2**141 * energy_budget < sampling_error**2
    assert 2**192 * energy_budget < injective_count**2
    assert amplitude_ceiling == 14_448_764_953_860_199_458_063_090_551_701_551
    assert period_ceiling == 85_047_155
    assert paley_ceiling == 46_341
    assert 1835 * paley_ceiling < period_ceiling < 1836 * paley_ceiling

    error_ratio_floor = sampling_error**2 // energy_budget
    aligned_ratio_floor = injective_count**2 // energy_budget

    print("BGK_SAMPLING_WITHOUT_REPLACEMENT_PRODUCTION_AUDIT")
    print(f"n={N} depth={DEPTH} coefficient={COEFFICIENT}")
    print(
        f"sampling_error_bits={sampling_error.bit_length()} "
        f"average_energy_budget_bits={energy_budget.bit_length()}"
    )
    print(
        f"sampling_error_sq_over_budget_floor_log2={error_ratio_floor.bit_length() - 1} "
        f"aligned_D7_sq_over_budget_floor_log2={aligned_ratio_floor.bit_length() - 1}"
    )
    print(
        f"hypothetical_D7_amplitude_ceiling={amplitude_ceiling} "
        f"coupling_period_ceiling={period_ceiling}"
    )
    print(
        f"paley_period_ceiling={paley_ceiling} "
        f"coupling_to_paley_ratio={period_ceiling / paley_ceiling:.9f}"
    )
    print(
        "VERDICT=generic without-replacement coupling misses by >141 energy bits and yields "
        "a period ceiling >1835 times Paley; subgroup mixing is load-bearing"
    )


if __name__ == "__main__":
    main()
