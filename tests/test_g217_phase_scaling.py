"""Unit coverage for scripts/probes/g217_phase_scaling_probe.py.

Tests the dyadic-subgroup primitives: group construction (exact order n),
the W(t) = #{y,z in G : 2y-z = t} profile, the R_r(t) subset-sum-difference
profile, and the discrete-log table.
"""

import sys
import types
from pathlib import Path

# Fake sympy before loading the probe (module-level `from sympy import ...`).
fake_sympy = types.ModuleType("sympy")
fake_sympy.primitive_root = lambda p: next(
    g for g in range(2, p)
    if pow(g, p - 1, p) == 1
    and all(pow(g, (p - 1) // q, p) != 1 for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37) if (p - 1) % q == 0)
)
fake_sympy.isprime = lambda n: n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
sys.modules["sympy"] = fake_sympy

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g217_phase_scaling_probe import (  # noqa: E402
    W_G_exact,
    build_group,
    dlog_table,
    R_r_exact,
)


def test_build_group_exact_order() -> None:
    G, g, m = build_group(257, 16)
    assert len(G) == 16
    assert m == 256 // 16  # (p-1)/n
    assert all(pow(x, 16, 257) == 1 for x in G)


def test_W_profile_sum() -> None:
    # sum_t W(t) = n^2 (each (y,z) pair contributes once).
    G, _, _ = build_group(257, 16)
    W = W_G_exact(257, G)
    assert sum(W) == 16 * 16
    # W(0) = n (y=z gives 2y-y = y... actually all y with z=y).
    assert W[0] == 16


def test_W_symmetry() -> None:
    # W(t) = W(-t) since 2y-z=t ⟺ 2z-y = ... check W(t)=W(-t) mod p.
    G, _, _ = build_group(97, 8)
    W = W_G_exact(97, G)
    for t in range(1, 97):
        assert W[t] == W[97 - t]


def test_R_profile_total() -> None:
    # sum_t R_r(t) = C(n,r) * C(n,r-1).
    G, _, _ = build_group(97, 8)
    R = R_r_exact(97, G, 2)
    import math

    assert sum(R) == math.comb(8, 2) * math.comb(8, 1)


def test_dlog_table() -> None:
    G, g, _ = build_group(17, 4)
    d = dlog_table(17, g)
    assert len(d) == 17
    for e in range(16):
        assert d[pow(g, e, 17)] == e
