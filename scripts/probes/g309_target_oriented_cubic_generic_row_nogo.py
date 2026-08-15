#!/usr/bin/env python3
"""Exact G309 control: odd-cubic positivity does not transfer on arbitrary nonnegative rows."""
from __future__ import annotations

import importlib.util
from pathlib import Path

BASE = Path(__file__).with_name("g302_common_order7_normal_nogo.py")
SPEC = importlib.util.spec_from_file_location("g302_base", BASE)
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


def odd_cubic_weight(j: int) -> int:
    return 0 if j % 3 == 0 else (1 if j % 3 == 1 else -1)


def main() -> None:
    n, p = 8, 73
    m = (p - 1) // n
    primitive = MOD.primitive_root(p)
    subgroup = MOD.subgroup(p, n, primitive)
    coeffs = [pow(2, j, p) for j in range(m)]
    assert m == 9
    assert subgroup == [1, 10, 27, 51, 72, 63, 46, 22]
    assert len({pow(a, n, p) for a in coeffs}) == m

    kernels = [MOD.weighted_kernel(subgroup, p, a) for a in coeffs]
    witnesses: list[tuple[int, int, int, list[int]]] = []
    for t in range(p):
        row = [0] * p
        row[t] = 1
        assert all(value >= 0 for value in row)
        values = [MOD.alignment(kernel, row, p, n) for kernel in kernels]
        target = values[1]
        odd = sum(odd_cubic_weight(j) * values[j] for j in range(m))
        if target < 0 < odd:
            witnesses.append((t, target, odd, values))

    assert len(witnesses) == 8
    first = witnesses[0]
    assert first == (4, -64, 73, [-64, -64, -64, 9, 82, 9, -64, 82, 82])
    print(f"cell n={n} p={p} quotient={m}")
    print(f"nonnegative delta-row counterexamples: {len(witnesses)}")
    print(f"first: t={first[0]} target={first[1]} odd={first[2]} values={first[3]}")
    print("PASS: generic nonnegative-row transfer is false; any surviving implication must use rank-row structure")


if __name__ == "__main__":
    main()
