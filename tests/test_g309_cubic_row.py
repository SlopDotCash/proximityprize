"""Unit coverage for scripts/probes/g309_target_oriented_cubic_generic_row_nogo.py.

Tests the odd-cubic weight function (0/1/-1 by j mod 3) and the G309
counterexample enumeration: 8 witnesses where target < 0 < odd, with the
recorded first witness exact values.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "probes"))

from g309_target_oriented_cubic_generic_row_nogo import (  # noqa: E402
    MOD,
    odd_cubic_weight,
)


def test_odd_cubic_weight_cycle() -> None:
    expected = {0: 0, 1: 1, 2: -1, 3: 0, 4: 1, 5: -1, 6: 0, 7: 1, 8: -1}
    for j, want in expected.items():
        assert odd_cubic_weight(j) == want


def test_odd_cubic_weight_negative_mod() -> None:
    # j = -1 → -1 % 3 = 2 → -1.
    assert odd_cubic_weight(-1) == -1
    assert odd_cubic_weight(-2) == 1  # -2 % 3 = 1


def test_g302_base_loaded() -> None:
    assert MOD is not None
    assert hasattr(MOD, "primitive_root")
    assert hasattr(MOD, "weighted_kernel")
    assert hasattr(MOD, "alignment")


def test_primitive_and_subgroup_matches_probe() -> None:
    n, p = 8, 73
    primitive = MOD.primitive_root(p)
    subgroup = MOD.subgroup(p, n, primitive)
    assert subgroup == [1, 10, 27, 51, 72, 63, 46, 22]


def test_witness_enumeration_matches_record() -> None:
    n, p, m = 8, 73, 9
    primitive = MOD.primitive_root(p)
    subgroup = MOD.subgroup(p, n, primitive)
    coeffs = [pow(2, j, p) for j in range(m)]
    kernels = [MOD.weighted_kernel(subgroup, p, a) for a in coeffs]
    witnesses = []
    for t in range(p):
        row = [0] * p
        row[t] = 1
        values = [MOD.alignment(kernel, row, p, n) for kernel in kernels]
        target = values[1]
        odd = sum(odd_cubic_weight(j) * values[j] for j in range(m))
        if target < 0 < odd:
            witnesses.append((t, target, odd, values))
    assert len(witnesses) == 8
    assert witnesses[0] == (4, -64, 73, [-64, -64, -64, 9, 82, 9, -64, 82, 82])
