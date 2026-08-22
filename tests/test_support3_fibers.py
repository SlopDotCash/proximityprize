"""Unit coverage for scripts/probes/probe_rate_quarter_support3_rational_fibers.py.

Tests the modular polynomial evaluation over F_17: Horner-style sum matches
direct power computation, and coefficients reduce mod p.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_rate_quarter_support3_rational_fibers import P, eval_poly  # noqa: E402


def test_eval_poly_constant() -> None:
    assert eval_poly([5], 3) == 5
    assert eval_poly([0], 3) == 0


def test_eval_poly_linear() -> None:
    # 2x + 3 at x=4 → 11 mod 17.
    assert eval_poly([3, 2], 4) == 11


def test_eval_poly_quadratic_matches_direct() -> None:
    coeffs = [1, 2, 3]  # 1 + 2x + 3x^2
    for x in range(P):
        direct = (1 + 2 * x + 3 * x * x) % P
        assert eval_poly(coeffs, x) == direct


def test_eval_poly_reduces_mod_p() -> None:
    # Coefficients larger than p wrap.
    assert eval_poly([P + 3], 1) == 3
    assert eval_poly([-1], 1) == P - 1


def test_eval_poly_x_at_boundary() -> None:
    # x = P → same as x = 0 mod p.
    coeffs = [1, 2, 3]
    assert eval_poly(coeffs, P) == eval_poly(coeffs, 0)
