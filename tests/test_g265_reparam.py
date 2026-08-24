"""Unit coverage for scripts/probes/g265_coordinate_reparametrization_nogo.py.

Tests the reparametrization primitives: prime factorization, primitive
root, subgroup construction, subset-sum histograms, exact circular
correlation, quotient profiling, multiplicative relabeling, centered
covariance, and primitive exponents.
"""

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g265_coordinate_reparametrization_nogo import (  # noqa: E402
    centered_cov,
    exact_corr,
    mul_relabel,
    prime_factors,
    primitive_exponents,
    primitive_root,
    quotient_profile,
    subgroup,
    subset_hists,
)


def test_prime_factors() -> None:
    assert prime_factors(12) == [2, 3]
    assert prime_factors(97) == [97]
    assert prime_factors(1) == []


def test_primitive_root() -> None:
    for p in (17, 97):
        g = primitive_root(p)
        assert pow(g, p - 1, p) == 1
        assert all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1))


def test_subgroup_order() -> None:
    G = subgroup(257, 16, primitive_root(257))
    assert len(G) == 16
    assert len(set(G)) == 16
    assert all(pow(x, 16, 257) == 1 for x in G)


def test_subset_hists_row_sums() -> None:
    G = subgroup(17, 8, primitive_root(17))
    dp = subset_hists(G, 17, 3)
    for r, row in enumerate(dp):
        assert sum(row) == math.comb(8, r)


def test_exact_corr_sum() -> None:
    a = [1, 2, 0, 1]
    b = [0, 1, 1, 0]
    out = exact_corr(a, b)
    assert sum(out) == sum(a) * sum(b)
    assert len(out) == 4


def test_mul_relabel_permutes() -> None:
    row = [1, 2, 3, 4]
    assert mul_relabel(row, 1) == row
    out = mul_relabel(row, 3)  # gcd(3,4)=1 → permutation
    assert sorted(out) == sorted(row)


def test_centered_cov() -> None:
    w = [1, 0, 1]
    r = [0, 1, 0]
    m = 3
    assert centered_cov(w, r) == m * sum(x * y for x, y in zip(w, r)) - sum(w) * sum(r)


def test_primitive_exponents() -> None:
    exps = primitive_exponents(17)
    assert 1 in exps
    assert 15 in exps  # gcd(15,16)=1
    assert 2 not in exps  # gcd(2,16)=2
    assert all(math.gcd(a, 16) == 1 for a in exps)


def test_quotient_profile_samples() -> None:
    field_row = [0] * 17
    field_row[3] = 5
    g = primitive_root(17)
    qp = quotient_profile(field_row, g, 4, 17)
    assert len(qp) == 4
    # pow(g, j, p) must hit 3 for exactly one j → one nonzero entry.
    assert sum(1 for v in qp if v) == 1
    assert 5 in qp
