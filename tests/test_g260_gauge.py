"""Unit coverage for scripts/probes/g260_origin_anchor_gauge_nogo.py.

Tests the gauge primitives: centered covariance, cyclic roll, unique argmax
(equivariant under roll), sign, and the exact Z/7 witness where a shift
sign-reverses the covariance but the gauge canonical form coincides.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g260_origin_anchor_gauge_nogo import cov, roll, sign, unique_argmax  # noqa: E402


def test_cov_formula() -> None:
    W = [2, 0, 1, 1, 1, 1, 0]
    R = [0, 0, 0, 1, 1, 1, 0]
    m = 7
    assert cov(W, R, m) == m * sum(w * r for w, r in zip(W, R)) - sum(W) * sum(R)


def test_roll_cyclic() -> None:
    assert roll([1, 2, 3, 4], 1) == [4, 1, 2, 3]
    assert roll([1, 2, 3, 4], 0) == [1, 2, 3, 4]
    assert roll([1, 2, 3, 4], 4) == [1, 2, 3, 4]  # full cycle


def test_unique_argmax() -> None:
    assert unique_argmax([1, 3, 2]) == 1
    assert unique_argmax([5, 1, 2]) == 0
    assert unique_argmax([2, 2, 1]) is None  # tie


def test_argmax_equivariant_under_roll() -> None:
    W = [2, 0, 1, 1, 1, 1, 0]
    m = len(W)
    a = unique_argmax(W)
    for c in range(m):
        Wc = roll(W, c)
        ac = unique_argmax(Wc)
        assert ac == (a + c) % m


def test_sign() -> None:
    assert sign(5) == 1
    assert sign(0) == 0
    assert sign(-3) == -1


def test_z7_witness() -> None:
    m = 7
    W = [2, 0, 1, 1, 1, 1, 0]
    R = [0, 0, 0, 1, 1, 1, 0]
    c = 2
    Wc = roll(W, c)
    assert cov(W, R, m) > 0
    assert cov(Wc, R, m) < 0
    # Gauge canonical forms coincide.
    a, ac = unique_argmax(W), unique_argmax(Wc)
    assert roll(W, -a) == roll(Wc, -ac)
