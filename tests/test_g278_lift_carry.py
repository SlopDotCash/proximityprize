"""Unit coverage for scripts/probes/g278_integer_lift_carry_exact.py.

Tests the integer-lift carry primitives: prime factorization, primitive
root, subgroup construction (exact order), and the lawful antipodal closed
forms.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g278_integer_lift_carry_exact import (  # noqa: E402
    lawful_antipodal,
    prime_factors,
    primitive_root,
    subgroup,
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


def test_subgroup_exact_order() -> None:
    for p, n in [(257, 16), (97, 8)]:
        G = subgroup(p, n)
        assert len(G) == n
        assert len(set(G)) == n
        assert all(0 < x < p for x in G)
        assert all(pow(x, n, p) == 1 for x in G)


def test_lawful_antipodal_forms() -> None:
    n = 16
    m = 8
    assert lawful_antipodal(n, 5) == n * (m - 2) * (m - 1) * (203 * m * m - 1099 * m + 1536) // 12
    assert lawful_antipodal(n, 6) == n * (m - 2) * (m - 1) * (287 * m**3 - 2789 * m * m + 9174 * m - 10160) // 20


def test_lawful_antipodal_positive() -> None:
    assert lawful_antipodal(2**30, 5) > 0
    assert lawful_antipodal(2**30, 6) > 0


def test_lawful_antipodal_unsupported() -> None:
    import pytest

    with pytest.raises(ValueError):
        lawful_antipodal(16, 7)
