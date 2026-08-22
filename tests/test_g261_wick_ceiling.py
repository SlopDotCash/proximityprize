"""Unit coverage for scripts/probes/g261_wick_ceiling_exceeds_dc_floor_probe.py.

Tests the exact Wick/DC floor primitives: odd double factorial, wick mass,
DC floor, the division-free identity, and the ratio law.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g261_wick_ceiling_exceeds_dc_floor_probe import (  # noqa: E402
    RESONANT,
    THIN,
    check_identity,
    dc_floor_num,
    odd_double_factorial,
    predicted_ratio,
    ratio,
    wick,
)


def test_odd_double_factorial() -> None:
    assert odd_double_factorial(0) == 1
    assert odd_double_factorial(1) == 1
    assert odd_double_factorial(2) == 3
    assert odd_double_factorial(3) == 15
    assert odd_double_factorial(4) == 105


def test_wick() -> None:
    assert wick(8, 3) == 15 * 8**3
    assert wick(2, 2) == 3 * 4


def test_dc_floor() -> None:
    assert dc_floor_num(8, 3) == 8**6
    assert dc_floor_num(2, 2) == 2**4


def test_check_identity_holds() -> None:
    for n in (8, 16, 32):
        for r in range(0, 10):
            assert check_identity(n, r)


def test_ratio_law() -> None:
    for n, q, r in RESONANT:
        assert abs(ratio(n, r, q) - predicted_ratio(n, r, q)) < 1e-9 * max(1.0, abs(predicted_ratio(n, r, q)))


def test_thin_regime_wick_gt_dc() -> None:
    # Thin regime (n^r <= q): wick > dc for r >= 2.
    for n, q, r in THIN:
        assert n**r <= q
        assert ratio(n, r, q) > 1
