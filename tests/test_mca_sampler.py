"""Unit coverage for scripts/proximity_prize_mca_sampler.py.

The math primitives are exact and testable at small field sizes:
Vandermonde codeword enumeration, power matrices, Lagrange interpolation
check, bad-gamma counting, and the pair-family samplers.
"""

import importlib.util
import random
import sys
from pathlib import Path

import numpy as np
import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "mca_sampler", str((Path(__file__).resolve().parents[1] / "scripts/proximity_prize_mca_sampler.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["mca_sampler"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_pow_mat() -> None:
    xs = np.array([0, 1, 2], dtype=np.int64)
    assert np.array_equal(mod.pow_mat(xs, 0, 3), np.array([1, 1, 1]))
    assert np.array_equal(mod.pow_mat(xs, 1, 3), xs)
    assert np.array_equal(mod.pow_mat(xs, 2, 3), np.array([0, 1, 1]))  # 2^2=4%3=1


def test_vandermonde_codewords_q2_k2() -> None:
    C = mod.vandermonde_codewords(2, 3, 2)
    # q=2, k=2 → 4 codewords of length n=3 over F2 (domain 0,1,2).
    assert C.shape == (4, 3)
    # All rows are distinct degree<2 polynomial evaluations.
    assert len({tuple(row) for row in C}) == 4
    # f(x) = a0 + a1*x over F2: x=2 ≡ 0 → f(2) == a0 == f(0).
    for row in C:
        assert row[2] == row[0]


def test_interpolate_check_linear() -> None:
    f = np.array([1, 2, 0], dtype=np.int64)  # f(x) = 1 + x over F3
    S = np.array([0, 1, 2], dtype=np.int64)
    assert mod.interpolate_check(f, S, 2, 3) is True


def test_interpolate_check_rejects_nonpolynomial() -> None:
    f = np.array([1, 2, 1], dtype=np.int64)  # not degree<2 over F3
    S = np.array([0, 1, 2], dtype=np.int64)
    assert mod.interpolate_check(f, S, 2, 3) is False


def test_interpolate_check_partial_set() -> None:
    # Degree<2 check on 2 points always passes (any 2 points fit a line).
    f = np.array([1, 2], dtype=np.int64)
    S = np.array([0, 1], dtype=np.int64)
    assert mod.interpolate_check(f, S, 2, 3) is True


def test_bad_gammas_clean_pair() -> None:
    # A pair already jointly explained everywhere has 0 bad gammas.
    C = mod.vandermonde_codewords(3, 4, 2)
    f1 = C[0].copy()
    f2 = C[1].copy()
    assert mod.bad_gammas_for_pair(f1, f2, C, 3, 4, 2, 0) == 0


def test_bad_gammas_random_pair_small() -> None:
    C = mod.vandermonde_codewords(3, 4, 2)
    rng = random.Random(42)
    f1 = np.array([rng.randrange(3) for _ in range(4)], dtype=np.int64)
    f2 = np.array([rng.randrange(3) for _ in range(4)], dtype=np.int64)
    count = mod.bad_gammas_for_pair(f1, f2, C, 3, 4, 2, 1)
    assert 0 <= count <= 3


def test_sample_pair_uniform() -> None:
    C = mod.vandermonde_codewords(5, 5, 2)
    rng = random.Random(7)
    f1, f2 = mod.sample_pair("uniform", C, 5, 5, 2, rng)
    assert f1.shape == (5,)
    assert f2.shape == (5,)
    assert np.all((f1 >= 0) & (f1 < 5))


def test_sample_pair_near_code() -> None:
    C = mod.vandermonde_codewords(5, 5, 2)
    rng = random.Random(8)
    f1, f2 = mod.sample_pair("near_code", C, 5, 5, 2, rng)
    assert f1.shape == (5,)
    # f1 is codeword + small error → close to some codeword.
    dists = (C != f1[None, :]).sum(axis=1)
    assert dists.min() <= 1


def test_sample_pair_rank_one() -> None:
    C = mod.vandermonde_codewords(5, 5, 2)
    rng = random.Random(9)
    f1, f2 = mod.sample_pair("rank_one", C, 5, 5, 2, rng)
    assert f1.shape == (5,)
    assert f2.shape == (5,)


def test_sample_pair_unknown_family() -> None:
    C = mod.vandermonde_codewords(5, 5, 2)
    with pytest.raises(ValueError):
        mod.sample_pair("bogus", C, 5, 5, 2, random.Random(1))


def test_sample_pair_deterministic_with_seed() -> None:
    C = mod.vandermonde_codewords(5, 5, 2)
    a = mod.sample_pair("uniform", C, 5, 5, 2, random.Random(99))
    b = mod.sample_pair("uniform", C, 5, 5, 2, random.Random(99))
    assert np.array_equal(a[0], b[0])
    assert np.array_equal(a[1], b[1])
