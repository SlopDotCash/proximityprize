"""Unit coverage for scripts/probes/g246_krylov_degree_two_countermodel.py.

Tests the countermodel setup: distinct prime factorization, primitive-root
construction, and the group/log-table setup (exact order n subgroup,
discrete-log table correctness).
"""

import sys
import types
from pathlib import Path

# Fake sympy before loading the probe (module-level `import sympy as sp`;
# only the setup primitives are under test, not the Matrix code).
fake_sympy = types.ModuleType("sympy")
fake_sympy.Matrix = list  # unused by the tested functions
sys.modules["sympy"] = fake_sympy

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g246_krylov_degree_two_countermodel import (  # noqa: E402
    factors,
    primitive_root,
    setup,
)


def test_factors_distinct() -> None:
    assert factors(12) == [2, 3]
    assert factors(97) == [97]
    assert factors(360) == [2, 3, 5]
    assert factors(1) == []


def test_primitive_root() -> None:
    for p in (17, 97, 257):
        g = primitive_root(p)
        assert pow(g, p - 1, p) == 1
        assert all(pow(g, (p - 1) // q, p) != 1 for q in factors(p - 1))


def test_setup_subgroup_order() -> None:
    m, g, logs, G = setup(257, 16)
    assert m == 16
    assert len(G) == 16
    assert len(set(G)) == 16
    assert all(pow(x, 16, 257) == 1 for x in G)


def test_setup_logs_correct() -> None:
    _, g, logs, _ = setup(17, 4)
    assert len(logs) == 17
    for e in range(16):
        assert logs[pow(g, e, 17)] == e


def test_setup_g_power_m_is_neg_one() -> None:
    # m = (p-1)/n and g primitive → g^m has order n (the subgroup generator).
    m, g, _, G = setup(257, 16)
    h = pow(g, m, 257)
    assert h in G
    assert pow(h, 16, 257) == 1
