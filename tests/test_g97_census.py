"""Unit coverage for scripts/probes/probe_466_g97_census_sup_inflation.py.

Tests prime factorization (with multiplicity), the 2-adic valuation v2,
and the character-spectrum construction (order-n subgroup of F_p^*,
non-trivial subgroup powers).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_466_g97_census_sup_inflation import (  # noqa: E402
    prime_factors,
    spectrum,
    v2,
)


def test_prime_factors_with_multiplicity() -> None:
    assert prime_factors(12) == [2, 2, 3]
    assert prime_factors(97) == [97]
    assert prime_factors(360) == [2, 2, 2, 3, 3, 5]
    assert prime_factors(1) == []


def test_prime_factors_product() -> None:
    import math

    for n in (12, 97, 360, 1024, 999983):
        fs = prime_factors(n)
        assert math.prod(fs) == n


def test_v2() -> None:
    assert v2(1) == 0
    assert v2(2) == 1
    assert v2(4) == 2
    assert v2(256) == 8
    assert v2(12) == 2  # 12 = 4*3
    assert v2(97) == 0  # odd


def test_spectrum_order_n() -> None:
    etas = spectrum(8, 257)
    assert etas is not None
    assert len(etas) == 257
    assert etas[0] == 8  # b=0 → sum over 8 roots = 8


def test_spectrum_max_below_n() -> None:
    etas = spectrum(16, 257)
    assert etas is not None
    M = max(etas[1:])
    assert M < 16  # non-principal characters never reach full mass
    assert M > 0
