"""Unit coverage for scripts/probes/g252_balanced_split_probe.py.

Tests the balanced-split primitives: trial-division primality and primitive
root construction (generates F_p^*).
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g252_balanced_split_probe import is_prime, primitive_root  # noqa: E402


def test_is_prime() -> None:
    assert is_prime(2)
    assert is_prime(101)
    assert is_prime(65537)
    assert not is_prime(1)
    assert not is_prime(4)
    assert not is_prime(100)


def test_primitive_root() -> None:
    for p in (17, 97, 257):
        g = primitive_root(p)
        assert g is not None
        assert pow(g, p - 1, p) == 1
        # Full order: powers cover all of F_p^*.
        assert len({pow(g, e, p) for e in range(p - 1)}) == p - 1


def test_primitive_root_large_prime() -> None:
    g = primitive_root(257)
    assert g is not None
    assert pow(g, 256, 257) == 1
    assert len({pow(g, e, 257) for e in range(256)}) == 256
