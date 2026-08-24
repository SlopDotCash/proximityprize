"""Unit coverage for scripts/probes/probe_bgk_depth9_wick_ratio.py.

Tests the multiplicative subgroup construction: the returned set has exact
order n and consists of n-th roots of unity in F_p, and the depth-9 energy
ratio is positive with the expected wick constant.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from probe_bgk_depth9_wick_ratio import DF17, depth_energy_ratio, subgroup  # noqa: E402


def test_subgroup_order_exact() -> None:
    for p, n in [(97, 8), (193, 16), (257, 16), (257, 32)]:
        G = subgroup(p, n)
        assert len(G) == n, f"n={n} order mismatch"
        assert len(set(G)) == n  # distinct


def test_subgroup_is_nth_roots() -> None:
    # Every element h satisfies h^n ≡ 1 mod p.
    p, n = 97, 8
    G = subgroup(p, n)
    for g in G:
        assert pow(g, n, p) == 1
    assert 1 in G


def test_subgroup_deterministic() -> None:
    assert subgroup(97, 8) == subgroup(97, 8)


def test_depth_energy_ratio_positive() -> None:
    Er, wick, ratio = depth_energy_ratio(97, 8)
    assert Er > 0
    assert wick == DF17 * float(8) ** 9
    assert ratio > 0


def test_wick_constant() -> None:
    assert DF17 == 34459425
