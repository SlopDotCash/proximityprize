"""Unit coverage for scripts/probes/probe_pair_locator_torus_fibers.py.

Tests projective normalization (scale first nonzero coordinate to 1) and
pair-value evaluation ((a-x)(a-y) mod p), plus the zero-vector rejection.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_pair_locator_torus_fibers import pair_value, projective  # noqa: E402


def test_projective_scales_first_nonzero() -> None:
    # (2, 4, 0) mod 17: scale by inv(2)=9 → (1, 4*9=36%17=2, 0).
    assert projective((2, 4, 0), 17) == (1, 2, 0)


def test_projective_identity() -> None:
    assert projective((1, 5, 7), 17) == (1, 5, 7)


def test_projective_negative_mod() -> None:
    # (-2, 0, 3) mod 17 → first nonzero -2 ≡ 15, inv(15)=8 → (1, 0, 24%17=7).
    assert projective((-2, 0, 3), 17) == (1, 0, 7)


def test_projective_zero_vector_rejected() -> None:
    with pytest.raises(ValueError, match="zero"):
        projective((0, 0, 0), 17)


def test_pair_value_basic() -> None:
    # (a - x)(a - y) mod p for each anchor a.
    assert pair_value(2, 5, (7,), 17) == ((7 - 2) * (7 - 5) % 17,)
    assert pair_value(2, 5, (7, 10), 17) == (10 % 17, (10 - 2) * (10 - 5) % 17)


def test_pair_value_zero_when_anchor_equals_petal() -> None:
    # If x == a, the product is 0.
    assert pair_value(7, 5, (7,), 17) == (0,)
