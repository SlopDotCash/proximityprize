"""Unit coverage for scripts/probes/probe_g90_spacing.py.

Tests the spacing-rigidity primitives: primality, prime search (p ≡ 1 mod
n), subgroup construction (exact order), star discrepancy, K-arc occupancy
discrepancy, multiplication-by-g branch count, and gap-count distinctness.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_g90_spacing import (  # noqa: E402
    branch_count,
    factorize,
    find_primes,
    gap_count,
    is_prime,
    star_discrepancy_count,
    subgroup,
    two_sided_disc,
)


def test_is_prime() -> None:
    assert is_prime(2)
    assert is_prime(101)
    assert is_prime(65537)
    assert not is_prime(1)
    assert not is_prime(100)


def test_find_primes_1mod() -> None:
    ps = find_primes(16, 100, 200, count=3)
    assert len(ps) == 2  # 113, 193 in [100,200]
    assert all(p % 16 == 1 for p in ps)
    assert all(is_prime(p) for p in ps)


def test_subgroup_exact_order() -> None:
    for p, n in [(257, 16), (1153, 32)]:
        S, g = subgroup(p, n)
        assert len(S) == n
        assert len(set(S)) == n
        assert all(pow(x, n, p) == 1 for x in S)
        assert pow(g, n, p) == 1


def test_star_discrepancy_uniform() -> None:
    # Equally spaced points have small discrepancy.
    p, n = 16, 4
    vals = [0, 4, 8, 12]
    D = star_discrepancy_count(vals, p)
    assert D <= n  # never exceeds n


def test_star_discrepancy_clustered() -> None:
    p, n = 16, 4
    vals = [0, 1, 2, 3]  # all clustered at start
    D = star_discrepancy_count(vals, p)
    assert D > 1  # large discrepancy


def test_two_sided_disc() -> None:
    p, n, K = 16, 4, 4
    vals = [0, 4, 8, 12]
    disc, cmax, cmin = two_sided_disc(vals, p, K)
    assert disc == 0  # exactly one per arc
    assert cmax == 1
    assert cmin == 1


def test_branch_count_rotation() -> None:
    # Use a real subgroup orbit: multiplication by g permutes it.
    p, n = 17, 8
    S, g = subgroup(p, n)
    runs, cyc = branch_count(S, g, p)
    assert runs >= 1
    assert cyc >= 1
    # A cyclic permutation has cyc_runs equal to the number of breaks;
    # for a genuine rotation orbit this is small (<= n/2 + 1 per E12).
    assert cyc <= n // 2 + 1


def test_gap_count_distinct() -> None:
    p, n = 16, 4
    vals = [0, 4, 8, 12]
    assert gap_count(vals, p) == 1  # single gap 4
    vals2 = [0, 1, 2, 3]
    assert gap_count(vals2, p) >= 2  # gaps 1, 13, ...


def test_factorize_distinct() -> None:
    assert factorize(12) == {2, 3}
    assert factorize(97) == {97}
    assert factorize(1) == set()
