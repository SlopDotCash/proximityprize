"""Unit coverage for scripts/probes/g263_joint_rank_sign_freedom_probe.py.

Tests the joint two-rank gate primitives: centered covariance, centered
functional (sum zero), the exact integer Plancherel identity, and 2x2 rank
via exact Fraction row reduction.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g263_joint_rank_sign_freedom_probe import (  # noqa: E402
    centered_cov,
    centered_functional,
    parseval_nonprincipal,
    rank_2x2,
)


def test_centered_functional_sums_to_zero() -> None:
    m, R = 5, [0, 1, 0, 1, 2]
    f = centered_functional(m, R)
    assert sum(f) == 0
    assert f == [m * x - sum(R) for x in R]


def test_centered_cov_matches_formula() -> None:
    m, W, R = 5, [1, 2, 0, 1, 0], [0, 1, 0, 1, 2]
    assert centered_cov(m, W, R) == m * sum(W[x] * R[x] for x in range(m)) - sum(W) * sum(R)


def test_parseval_equals_centered_cov() -> None:
    m, W, R = 5, [1, 2, 0, 1, 0], [0, 1, 0, 1, 2]
    assert parseval_nonprincipal(m, W, R) == centered_cov(m, W, R)


def test_parseval_zero_for_constant() -> None:
    # W constant → nonprincipal projection vanishes.
    m = 5
    W = [3] * m
    R = [0, 1, 0, 1, 2]
    assert parseval_nonprincipal(m, W, R) == 0


def test_rank_2x2_independent_rows() -> None:
    rows = [[1, 0], [0, 1]]
    assert rank_2x2(rows) == 2


def test_rank_2x2_dependent_rows() -> None:
    rows = [[1, 2], [2, 4]]
    assert rank_2x2(rows) == 1


def test_rank_2x2_zero_row() -> None:
    rows = [[0, 0], [1, 1]]
    assert rank_2x2(rows) == 1


def test_rank_2x2_fraction_exact() -> None:
    rows = [[1, 3], [2, 6]]
    assert rank_2x2(rows) == 1  # 2 = 2*1, 6 = 2*3 exactly
