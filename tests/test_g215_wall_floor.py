"""Unit coverage for scripts/probes/g215_sharp_dyadic_wall_floor.py.

Tests the flat-partition minimiser sumsq_flat(m) = 1 + 4(m-1), the sharp
tail floor identity n^2*(2n-3), and the Cauchy-Schwarz gap inequalities at
both tail and wall levels.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g215_sharp_dyadic_wall_floor import sumsq_flat  # noqa: E402


def test_sumsq_flat_small() -> None:
    assert sumsq_flat(2) == 1 + 4  # [1,2] → 1 + 4 = 5
    assert sumsq_flat(3) == 1 + 8  # [1,2,2] → 1 + 4 + 4 = 9
    assert sumsq_flat(4) == 1 + 12  # [1,2,2,2] → 13


def test_sumsq_flat_formula() -> None:
    for m in range(2, 50):
        assert sumsq_flat(m) == 1 + 4 * (m - 1)


def test_flat_equals_2n_minus_3() -> None:
    for m in range(2, 100):
        n = 2 * m
        assert sumsq_flat(m) == 2 * n - 3


def test_tail_sharp_identity() -> None:
    for m in range(2, 50):
        n = 2 * m
        flat = sumsq_flat(m)
        assert n * n * flat == n * n * (2 * n - 3)


def test_cs_gap_holds() -> None:
    for m in range(2, 100):
        n = 2 * m
        tail_sharp = n * n * (2 * n - 3)
        cs_tail = 2 * n * (n - 1) ** 2
        assert cs_tail < tail_sharp
        wall_sharp = n * (2 * n - 3)
        wall_cs = 2 * (n - 1) ** 2
        assert wall_cs < wall_sharp
        assert tail_sharp // n == wall_sharp
