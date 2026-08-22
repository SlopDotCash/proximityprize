"""Unit coverage for scripts/probes/g281_carry_shape_amplification_nogo.py.

Tests the exact antipodal/zero-carry floor closed forms (G278) and the
covariance mass, plus the certificate inequality on the sponsor cells.
"""

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g281_carry_shape_amplification_nogo import (  # noqa: E402
    PI_EXACT,
    PI_LOWEST,
    antipodal_closed,
    covariance_mass,
)


def test_antipodal_closed_small_even() -> None:
    n = 16
    m = 8
    # r=5 closed form: n*(m-2)*(m-1)*(203m^2-1099m+1536)//12.
    expect5 = n * (m - 2) * (m - 1) * (203 * m * m - 1099 * m + 1536) // 12
    assert antipodal_closed(n, 5) == expect5
    expect6 = n * (m - 2) * (m - 1) * (287 * m**3 - 2789 * m * m + 9174 * m - 10160) // 20
    assert antipodal_closed(n, 6) == expect6


def test_antipodal_closed_positive() -> None:
    for r in (5, 6):
        assert antipodal_closed(2**30, r) > 0


def test_antipodal_closed_unsupported_rank() -> None:
    import pytest

    with pytest.raises(ValueError):
        antipodal_closed(16, 7)


def test_covariance_mass() -> None:
    n, r = 16, 5
    from math import comb

    assert covariance_mass(n, r) == n * n * comb(n, r) * comb(n, r - 1)


def test_pi_lower_bounds_valid() -> None:
    for r in (5, 6):
        assert Fraction(*PI_LOWEST[r]) <= PI_EXACT[r]


def test_certificate_holds_on_sponsors() -> None:
    n = 2**30
    for p in (n * (2**128 + 192) + 1, n * (2**129 + 13) + 1):
        for r in (5, 6):
            L = antipodal_closed(n, r)
            B = covariance_mass(n, r)
            num, den = PI_LOWEST[r]
            assert L * p * den < B * num, f"certificate failed r={r}"
