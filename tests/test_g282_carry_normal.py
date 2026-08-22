"""Unit coverage for scripts/probes/g282_carry_fourier_normal_probe.py.

Tests the exact-integer number-theory primitives: Möbius function, Euler
phi, Ramanujan sums (exact c_d(k)), and the sign function.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g282_carry_fourier_normal_probe import mobius, phi, ramanujan, sgn  # noqa: E402


def test_sgn() -> None:
    assert sgn(5) == 1
    assert sgn(0) == 0
    assert sgn(-3) == -1


def test_mobius_values() -> None:
    assert mobius(1) == 1
    assert mobius(2) == -1
    assert mobius(3) == -1
    assert mobius(4) == 0  # 2^2
    assert mobius(6) == 1  # 2*3
    assert mobius(30) == -1  # 2*3*5


def test_phi_values() -> None:
    assert phi(1) == 1
    assert phi(2) == 1
    assert phi(3) == 2
    assert phi(6) == 2
    assert phi(12) == 4
    assert phi(97) == 96


def test_ramanujan_sum_basic() -> None:
    # c_1(k) = 1 for all k (a mod 1: (a,1)=1, only a=0; exp(0)=1).
    assert ramanujan(1, 0) == 1
    assert ramanujan(1, 5) == 1


def test_ramanujan_sum_k0() -> None:
    # c_d(0) = phi(d).
    assert ramanujan(6, 0) == phi(6) == 2
    assert ramanujan(12, 0) == phi(12) == 4


def test_ramanujan_consistency() -> None:
    # c_d(k) = c_d(k+d) (periodicity).
    for d in (4, 6, 12):
        for k in range(d):
            assert ramanujan(d, k) == ramanujan(d, k + d)


def test_ramanujan_gcd_reduction() -> None:
    # c_4(2) = μ(4/gcd(4,2))·φ(4)/φ(4/gcd(4,2)) = μ(2)·φ(4)/φ(2) = -1·2/1 = -2.
    assert ramanujan(4, 2) == -2
    # Direct: a ∈ {1,3} mod 4 → exp(πi) + exp(3πi) = -1 + -1 = -2. ✓
