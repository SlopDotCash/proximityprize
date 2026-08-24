"""Unit coverage for scripts/probes/probe_g180_center_forcing.py.

Tests the central-symmetry primitives: vma (minimal absolute residue),
orbit (multiplicative orbit of x under b), and fits_interval (all orbit
points within natAbs V of center a).

sympy is unavailable in the test env, so it is faked at load time (the probe
only uses isprime/primitive_root at module level for its demo loop, which
the test never runs).
"""

import sys
import types
from pathlib import Path

# Fake sympy before loading the probe (module-level `from sympy import ...`).
fake_sympy = types.ModuleType("sympy")
fake_sympy.isprime = lambda n: n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
fake_sympy.primitive_root = lambda p: next(g for g in range(2, p) if pow(g, p - 1, p) == 1 and all(pow(g, (p - 1) // q, p) != 1 for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37) if (p - 1) % q == 0))
sys.modules["sympy"] = fake_sympy

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_g180_center_forcing import fits_interval, orbit, vma  # noqa: E402


def test_vma_minimal_absolute() -> None:
    assert vma(3, 7) == 3
    assert vma(5, 7) == -2  # 5 > 3.5 → 5-7
    assert vma(0, 7) == 0
    assert vma(-1, 7) == -1  # -1 % 7 = 6 → 6 > 3.5 → 6-7 = -1


def test_vma_wraps_negative() -> None:
    assert vma(-3, 7) == -3
    assert vma(10, 7) == 3  # 10 % 7 = 3


def test_orbit_starts_at_b() -> None:
    # x = 2, n = 3, p = 7: orbit = [b*2^0, b*2^1, b*2^2] mod 7.
    assert orbit(7, 2, 1, 3) == [1, 2, 4]
    assert orbit(7, 2, 3, 3) == [3, 6, 5]


def test_orbit_order() -> None:
    # x = 2 mod 7 has order 3 (2^3 = 8 ≡ 1): orbit length 3, all distinct.
    o = orbit(7, 2, 1, 3)
    assert len(set(o)) == 3


def test_fits_interval_centered() -> None:
    O = [1, 2, 4]
    assert fits_interval(O, 7, 0, 4)  # all within 4 of 0
    assert not fits_interval(O, 7, 0, 1)  # 4 is too far


def test_fits_interval_off_center() -> None:
    O = [1, 2, 4]
    # Center 3: distances |1-3|=2, |2-3|=1, |4-3|=1 → fits V=2.
    assert fits_interval(O, 7, 3, 2)
    assert not fits_interval(O, 7, 3, 0)
