"""Unit coverage for scripts/probes/probe_syz34.py.

Tests the F_p linear-algebra primitives: rref rank, dual-basis construction
on a support (null space of the Vandermonde), and intersection dimension
via dim U + dim V - dim(U+V).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_syz34 import dual_basis_on_support, intersect_dim, rref_dim  # noqa: E402


def test_rref_dim_zero_rows() -> None:
    assert rref_dim([], 3, 7) == 0


def test_rref_dim_full_rank() -> None:
    rows = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    assert rref_dim(rows, 3, 7) == 3


def test_rref_dim_dependent_rows() -> None:
    rows = [[1, 2, 3], [2, 4, 6], [1, 1, 1]]
    assert rref_dim(rows, 3, 7) == 2  # row2 = 2*row1


def test_rref_dim_mod_reduction() -> None:
    rows = [[3, 0], [0, 3]]  # over F_2 both ≡ 1
    assert rref_dim(rows, 2, 2) == 2


def test_dual_basis_support_small() -> None:
    # n=4, k=2, support {0,1}: dual vectors on 2 points satisfy
    # v0 + v1 = 0 and v0*x0 + v1*x1 = 0 → v0=v1=0 → no nonzero basis.
    x = [1, 2, 3, 4]  # eval points
    basis = dual_basis_on_support(x, 2, {0, 1}, 7)
    assert basis == []


def test_dual_basis_support_three_points() -> None:
    # n=4, k=2, support {0,1,2}: dim = max(0, 3-2) = 1.
    x = [1, 2, 3, 4]
    basis = dual_basis_on_support(x, 2, {0, 1, 2}, 7)
    assert len(basis) == 1
    v = basis[0]
    # v satisfies sum_j v_j = 0 and sum_j v_j x_j = 0.
    assert sum(v) % 7 == 0
    assert sum(v[j] * x[j] for j in range(4)) % 7 == 0
    assert all(v[j] == 0 for j in range(3, 4))  # supported on S


def test_intersect_dim_formula() -> None:
    # U = span(e1), V = span(e2) in F_7^3 → intersection 0.
    U = [[1, 0, 0]]
    V = [[0, 1, 0]]
    assert intersect_dim(U, V, 3, 7) == 0
    # U = span(e1, e2), V = span(e2) → intersection 1.
    U2 = [[1, 0, 0], [0, 1, 0]]
    V2 = [[0, 1, 0]]
    assert intersect_dim(U2, V2, 3, 7) == 1
