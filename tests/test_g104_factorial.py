"""Unit coverage for scripts/probes/probe_466_g104_primitive_concentration_factorial_no_go.py.

Tests the odd double factorial, the certified order-2^30 element powers
(distinct subset sums), and the factorial-vs-threshold inequalities that
constitute the no-go countercertificate.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

import probe_466_g104_primitive_concentration_factorial_no_go as mod  # noqa: E402


def test_odd_double_factorial_values() -> None:
    # range(1, m+1, 2): product of odds ≤ m.
    assert mod.odd_double_factorial(1) == 1
    assert mod.odd_double_factorial(3) == 3  # 1*3
    assert mod.odd_double_factorial(5) == 15  # 1*3*5
    assert mod.odd_double_factorial(7) == 105  # 1*3*5*7


def test_odd_double_factorial_matches_math() -> None:
    from math import prod

    for m in (1, 3, 5, 9, 13):
        assert mod.odd_double_factorial(m) == prod(range(1, m + 1, 2))


def test_powers_distinct_and_order() -> None:
    assert len(set(mod.xs)) == mod.K
    assert all(pow(x, mod.N, mod.P) == 1 for x in mod.xs)


def test_subset_sums_distinct() -> None:
    # Module-level assertions already ran at import; verify the claim holds.
    subset_sums = {}
    for mask in range(1 << mod.K):
        total = sum(mod.xs[i] for i in range(mod.K) if mask >> i & 1) % mod.P
        assert total not in subset_sums
        subset_sums[total] = mask
    assert subset_sums[0] == 0
    assert len(subset_sums) == 1 << mod.K


def test_factorial_exceeds_thresholds() -> None:
    from math import comb, factorial

    floor = factorial(mod.K)
    assert floor > mod.actual_threshold
    assert floor > mod.uniform_threshold
