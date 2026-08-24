"""Unit coverage for scripts/probes/g240_quotient_incidence_probe.py.

Tests the quotient-incidence primitives: prime factorization and primitive
root construction (generates F_p^*).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g240_quotient_incidence_probe import factors, proot  # noqa: E402


def test_factors() -> None:
    # Distinct prime factors (no multiplicity).
    assert factors(12) == [2, 3]
    assert factors(97) == [97]
    assert factors(360) == [2, 3, 5]
    assert factors(1) == []


def test_factors_product() -> None:
    # Product of distinct primes equals squarefree kernel (not n itself).
    import math

    assert math.prod(factors(12)) == 6  # 2*3
    assert math.prod(factors(360)) == 30  # 2*3*5
    assert math.prod(factors(97)) == 97
    assert math.prod(factors(65537)) == 65537


def test_proot_generates() -> None:
    for p in (17, 97, 257):
        g = proot(p)
        assert pow(g, p - 1, p) == 1
        assert all(pow(g, (p - 1) // q, p) != 1 for q in factors(p - 1))


def test_proot_order_full() -> None:
    # g has order p-1: the set of powers covers all of F_p^*.
    g = proot(17)
    powers = {pow(g, e, 17) for e in range(16)}
    assert powers == set(range(1, 17))
