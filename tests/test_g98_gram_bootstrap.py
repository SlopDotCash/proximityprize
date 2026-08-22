"""Unit coverage for scripts/probes/probe_g98_gram_bootstrap.py.

Tests the number-theory primitives: Miller-Rabin primality, factorization,
primitive-root construction, and the BSGS discrete-log class (Dlog)
including the baby-step table and giant-step inverse.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_g98_gram_bootstrap import Dlog, factorize, is_prime, primitive_root  # noqa: E402


def test_is_prime() -> None:
    assert is_prime(2)
    assert is_prime(101)
    assert is_prime(10007)
    assert not is_prime(1)
    assert not is_prime(4)
    assert not is_prime(100)


def test_factorize() -> None:
    assert factorize(12) == {2: 2, 3: 1}
    assert factorize(97) == {97: 1}
    assert factorize(360) == {2: 3, 3: 2, 5: 1}
    assert factorize(1) == {}


def test_primitive_root() -> None:
    p = 17
    g = primitive_root(p)
    # g generates F_p^*: order p-1 = 16.
    assert pow(g, 16, p) == 1
    assert all(pow(g, (p - 1) // q, p) != 1 for q in factorize(p - 1))


def test_dlog_roundtrip() -> None:
    p, g = 17, primitive_root(17)
    dlog = Dlog(g, p)
    for x in (1, 2, 3, 5, 7, 11, 16):
        e = dlog(x)
        assert pow(g, e, p) == x


def test_dlog_consistency() -> None:
    p, g = 101, primitive_root(101)
    dlog = Dlog(g, p)
    # dlog(a*b) = dlog(a) + dlog(b) mod (p-1).
    a, b = 23, 47
    assert dlog(a * b % p) == (dlog(a) + dlog(b)) % (p - 1)


def test_dlog_small_prime() -> None:
    p, g = 7, primitive_root(7)
    dlog = Dlog(g, p)
    for x in range(1, 7):
        assert pow(g, dlog(x), p) == x
