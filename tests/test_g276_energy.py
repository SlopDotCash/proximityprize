"""Unit coverage for scripts/probes/g276_energy_witnesses.py.

Tests the energy-witness primitives: primality, prime factorization,
primitive root, subgroup construction (exact order), and the cell Cauchy-
Schwarz invariant (signed² <= E_W·E_R) on a small cell.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g276_energy_witnesses import (  # noqa: E402
    cell,
    is_prime,
    prime_factors,
    primitive_root,
    subgroup,
)


def test_is_prime() -> None:
    assert is_prime(2)
    assert is_prime(101)
    assert is_prime(65537)
    assert not is_prime(1)
    assert not is_prime(4)
    assert not is_prime(100)


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
        G, root = subgroup(p, n)
        assert len(G) == n
        assert len(set(G)) == n
        assert all(pow(x, n, p) == 1 for x in G)


def test_cell_cauchy_schwarz() -> None:
    z = cell(113, 8, 3)
    assert z["E_W"] >= 0
    assert z["E_R"] >= 0
    assert z["signed"] * z["signed"] <= z["E_W"] * z["E_R"]


def test_cell_parseval_identity() -> None:
    # The cell asserts (p*W0-SW)(p*R0-SR) + n*Σ wq·rq == p*A internally.
    z = cell(113, 8, 4)
    assert z["A"] is not None
