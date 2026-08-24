"""Unit coverage for scripts/probes/probe_bgk_h8_transition_integrality.py.

Tests the normalized subset-discrepancy function on H8 < F_17: exact
Fraction deviations, the transition ratios c_r = n Z_{r+1}/Z_r, and the
core claim that five of six ratios are nonintegral.
"""

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_bgk_h8_transition_integrality import (  # noqa: E402
    H8,
    Q,
    normalized_subset_deviation,
)


def test_deviation_r1() -> None:
    # r=1: sums are the elements themselves; energy is a known exact value.
    dev = normalized_subset_deviation(1)
    assert dev == Fraction(153, 8)


def test_deviation_r2() -> None:
    assert normalized_subset_deviation(2) == Fraction(51, 14)


def test_deviation_symmetric() -> None:
    # C(8,r) = C(8,8-r); deviations should be symmetric in r.
    assert normalized_subset_deviation(1) == normalized_subset_deviation(7)
    assert normalized_subset_deviation(2) == normalized_subset_deviation(6)
    assert normalized_subset_deviation(3) == normalized_subset_deviation(5)


def test_all_deviations_match_record() -> None:
    deviations = [normalized_subset_deviation(r) for r in range(1, 8)]
    expected = [
        Fraction(153, 8), Fraction(51, 14), Fraction(561, 392),
        Fraction(204, 175), Fraction(561, 392), Fraction(51, 14),
        Fraction(153, 8),
    ]
    assert deviations == expected


def test_ratios_five_of_six_nonintegral() -> None:
    deviations = [normalized_subset_deviation(r) for r in range(1, 8)]
    ratios = [Fraction(len(H8)) * deviations[r] / deviations[r - 1]
              for r in range(1, 7)]
    expected = [
        Fraction(32, 21), Fraction(22, 7), Fraction(1792, 275),
        Fraction(275, 28), Fraction(224, 11), Fraction(42, 1),
    ]
    assert ratios == expected
    assert sum(r.denominator != 1 for r in ratios) == 5


def test_group_size() -> None:
    assert Q == 17
    assert len(H8) == 8
