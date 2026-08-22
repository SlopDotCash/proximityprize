"""Unit coverage for scripts/probes/g262_sponsor_rank_crossover_probe.py.

Tests the exact sponsor rank-5/rank-6 Wick/DC crossover: odd double
factorials, the exact Fraction ratio, and the crossover direction flips
between adjacent ranks at both sponsor primes.
"""

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g262_sponsor_rank_crossover_probe import (  # noqa: E402
    N,
    SPONSORS,
    odd_double_factorial,
    ratio_wick_to_dc,
)


def test_odd_double_factorial_values() -> None:
    assert odd_double_factorial(1) == 1
    assert odd_double_factorial(2) == 3
    assert odd_double_factorial(3) == 15
    assert odd_double_factorial(4) == 105
    assert odd_double_factorial(5) == 945
    assert odd_double_factorial(6) == 10395


def test_ratio_wick_to_dc_exact_fraction() -> None:
    q = N * (2**128 + 192) + 1
    r5 = ratio_wick_to_dc(q, 5)
    assert isinstance(r5, Fraction)
    # ((2*5-1)!! * q) / N^5 → numerator/denominator exact.
    assert r5 == Fraction(odd_double_factorial(5) * q, N**5)


def test_crossover_direction_flips() -> None:
    # rank 5: Wick dominates DC; rank 6: DC dominates Wick.
    for q in SPONSORS.values():
        assert ratio_wick_to_dc(q, 5) > 1
        assert ratio_wick_to_dc(q, 6) < 1


def test_sponsor_magnitude_between_n5_n6() -> None:
    for q in SPONSORS.values():
        assert N**5 < q < N**6


def test_exact_margins_p1() -> None:
    q = SPONSORS["P1"]
    assert ratio_wick_to_dc(q, 5) > 241_920
    assert ratio_wick_to_dc(q, 6) < Fraction(1, 400)
    assert 400 * odd_double_factorial(6) * N**6 * q < N**12


def test_exact_margins_p2() -> None:
    q = SPONSORS["P2"]
    assert ratio_wick_to_dc(q, 5) > 483_840
    assert ratio_wick_to_dc(q, 6) < Fraction(1, 200)
    assert 200 * odd_double_factorial(6) * N**6 * q < N**12
