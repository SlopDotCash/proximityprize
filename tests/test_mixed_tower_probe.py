"""Unit coverage for docs/kb/mixed-tower-probes/mixed_tower_probe.py.

Tests the arithmetic primitives: Miller-Rabin primality, prime search
(p ≡ 1 mod n), prime factorization, primitive-root-of-unity construction,
divisor enumeration, and the divisibility-minimal allowed-divisor set for
the packet-union prediction.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "docs" / "kb" / "mixed-tower-probes"))

from mixed_tower_probe import (  # noqa: E402
    coset_blocks,
    divisors,
    find_prime_1mod,
    is_prime,
    min_allowed,
    prime_factors,
    primitive_root_of_unity,
)


def test_is_prime_small() -> None:
    assert is_prime(2)
    assert is_prime(3)
    assert is_prime(101)
    assert not is_prime(1)
    assert not is_prime(4)
    assert not is_prime(100)


def test_is_prime_large() -> None:
    assert is_prime(1_000_000_007)
    assert not is_prime(1_000_000_000)


def test_find_prime_1mod() -> None:
    p = find_prime_1mod(72, 10**9)
    assert p >= 10**9
    assert p % 72 == 1
    assert is_prime(p)


def test_prime_factors() -> None:
    assert prime_factors(12) == {2, 3}
    assert prime_factors(72) == {2, 3}
    assert prime_factors(101) == {101}
    assert prime_factors(1) == set()


def test_primitive_root_of_unity() -> None:
    p = 97  # 96 = 3*2^5, 97-1 divisible by 6? 96/6=16 yes
    z = primitive_root_of_unity(6, p)
    assert pow(z, 6, p) == 1
    assert z != 1
    assert pow(z, 2, p) != 1
    assert pow(z, 3, p) != 1


def test_divisors() -> None:
    assert divisors(12) == [1, 2, 3, 4, 6, 12]
    assert divisors(1) == [1]


def test_min_allowed() -> None:
    # n=12, t=4: divisors >4 are {6,12}; 12 % 6 == 0 → 6 is minimal.
    assert min_allowed(12, 4) == (6,)
    # n=12, t=2: divisors >2 {3,4,6,12}; minimal: 3,4 (6,12 divisible).
    assert min_allowed(12, 2) == (3, 4)
    # n=8, t=3: divisors >3 {4,8}; 4 minimal.
    assert min_allowed(8, 3) == (4,)


def test_coset_blocks() -> None:
    # n=6, d=2: cosets of mu_2 → {0,3},{1,4},{2,5} (3 blocks of size 2).
    blocks = coset_blocks(6, (2,))
    assert len(blocks) == 3
    assert all(b.bit_count() == 2 for b in blocks)
    # Union covers all of mu_6.
    union = 0
    for b in blocks:
        union |= b
    assert union == (1 << 6) - 1
