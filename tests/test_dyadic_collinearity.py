"""Unit coverage for scripts/probes/probe_dyadic_pair_quadratic_collinearity.py.

Tests modular inversion (Fermat), line normalization (scale to first
nonzero coordinate = 1), and the zero-line rejection.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_dyadic_pair_quadratic_collinearity import inv, normalize_line  # noqa: E402


def test_inv_basic() -> None:
    assert inv(2, 17) == 9  # 2*9 = 18 ≡ 1
    assert inv(3, 17) == 6  # 3*6 = 18 ≡ 1
    assert inv(1, 17) == 1


def test_inv_negative_mod() -> None:
    assert inv(-1, 17) == 16
    assert inv(-2, 17) == inv(15, 17)


def test_inv_zero_returns_zero() -> None:
    # pow(0, p-2, p) = 0 (Fermat edge; matches implementation).
    assert inv(0, 17) == 0


def test_normalize_line_scales_first_nonzero() -> None:
    # (2, 0, 4) mod 17: scale by inv(2)=9 → (1, 0, 4*9=36%17=2).
    assert normalize_line(2, 0, 4, 17) == (1, 0, 2)


def test_normalize_line_skips_zero_leading() -> None:
    # (0, 3, 6) mod 17: first nonzero is 3 → scale by 6 → (0, 1, 2).
    assert normalize_line(0, 3, 6, 17) == (0, 1, 2)


def test_normalize_line_identity() -> None:
    # Already normalized → unchanged.
    assert normalize_line(1, 5, 7, 17) == (1, 5, 7)


def test_normalize_line_zero_line_rejected() -> None:
    with pytest.raises(ValueError, match="zero"):
        normalize_line(0, 0, 0, 17)
