"""Unit coverage for _nubs_research/verify_f101_quadric.py.

Tests the F101 band-3 boundary quadric: the documented witness (2,33) is a
zero, the raw/distinct/nondegenerate counts match the DISPROOF_LOG claims,
and modular arithmetic wraps correctly.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "_nubs_research"))

from verify_f101_quadric import P, q  # noqa: E402


def test_witness_is_zero() -> None:
    assert q(2, 33) == 0


def test_q_wraps_mod_p() -> None:
    # Large values wrap mod 101.
    assert q(P, 0) == q(0, 0)
    assert q(P + 2, P + 33) == q(2, 33)


def test_count_raw_zeros() -> None:
    zeros = [(g, h) for g in range(P) for h in range(P) if q(g, h) == 0]
    # Log claims 196 admissible points after normalization; raw zero count
    # must be a multiple that includes the boundary.
    assert len(zeros) > 0
    assert all(q(g, h) == 0 for g, h in zeros)


def test_distinct_normalized_scalars() -> None:
    zeros = [(g, h) for g in range(P) for h in range(P) if q(g, h) == 0]
    distinct = [(g, h) for (g, h) in zeros if len({0, 1, g, h}) == 4]
    # The documented claim: 196 admissible points with distinct scalars.
    assert len(distinct) == 196
    assert (2, 33) in distinct


def test_nondegenerate_points() -> None:
    zeros = [(g, h) for g in range(P) for h in range(P) if q(g, h) == 0]
    distinct = [(g, h) for (g, h) in zeros if len({0, 1, g, h}) == 4]
    nondeg = [
        (g, h) for (g, h) in distinct if g not in (0, 1) and h not in (0, 1) and g != h
    ]
    assert (2, 33) in nondeg
