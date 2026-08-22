"""Unit coverage for scripts/probes/g242_carrier_correct_quotient_largesieve_probe.py.

Tests the primitive-root construction used by the quotient large-sieve
cells: generates F_p^* (full order) across small and larger primes.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g242_carrier_correct_quotient_largesieve_probe import primitive_root  # noqa: E402


def test_primitive_root_small_primes() -> None:
    for p in (17, 97):
        g = primitive_root(p)
        assert g is not None
        assert pow(g, p - 1, p) == 1
        assert len({pow(g, e, p) for e in range(p - 1)}) == p - 1


def test_primitive_root_larger_prime() -> None:
    g = primitive_root(257)
    assert g is not None
    assert pow(g, 256, 257) == 1
    assert len({pow(g, e, 257) for e in range(256)}) == 256


def test_primitive_root_rejects_subgroup_powers() -> None:
    # For each prime factor f of p-1, g^((p-1)/f) != 1.
    g = primitive_root(17)
    for f in (2,):  # 16 = 2^4
        assert pow(g, 16 // f, 17) != 1
