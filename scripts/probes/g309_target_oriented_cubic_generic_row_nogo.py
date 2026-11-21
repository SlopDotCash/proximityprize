#!/usr/bin/env python3
"""Exact G309 control: odd-cubic positivity does not transfer on arbitrary nonnegative rows."""
from __future__ import annotations

import importlib.util
from pathlib import Path

BASE = Path(__file__).with_name("g302_common_order7_normal_nogo.py")
SPEC = importlib.util.spec_from_file_location("g302_base", BASE)
MOD = importlib.util.module_from_spec(SPEC)
if SPEC.loader is None:
    raise ImportError(f"could not load shared exact arithmetic helper from {BASE}")
SPEC.loader.exec_module(MOD)


def require(condition: bool, message: str) -> None:
    """Keep the G309 exact counterexample certificate active under optimization."""
    if not condition:
        raise AssertionError(message)


def odd_cubic_weight(j: int) -> int:
    return 0 if j % 3 == 0 else (1 if j % 3 == 1 else -1)


def main() -> None:
    n, p = 8, 73
    m = (p - 1) // n
    primitive = MOD.primitive_root(p)
    subgroup = MOD.subgroup(p, n, primitive)
    coeffs = [pow(2, j, p) for j in range(m)]
    require(m == 9, f"G309 quotient order changed: {m}")
    require(
        subgroup == [1, 10, 27, 51, 72, 63, 46, 22],
        f"G309 subgroup pin failed: {subgroup}",
    )
    require(len({pow(a, n, p) for a in coeffs}) == m, "G309 coefficient powers are not distinct")

    kernels = [MOD.weighted_kernel(subgroup, p, a) for a in coeffs]
    witnesses: list[tuple[int, int, int, list[int]]] = []
    for t in range(p):
        row = [0] * p
        row[t] = 1
        require(all(value >= 0 for value in row), f"G309 delta row at t={t} is not nonnegative")
        values = [MOD.alignment(kernel, row, p, n) for kernel in kernels]
        target = values[1]
        odd = sum(odd_cubic_weight(j) * values[j] for j in range(m))
        if target < 0 < odd:
            witnesses.append((t, target, odd, values))

    require(len(witnesses) == 8, f"G309 counterexample count changed: {len(witnesses)}")
    first = witnesses[0]
    require(
        first == (4, -64, 73, [-64, -64, -64, 9, 82, 9, -64, 82, 82]),
        f"G309 exact target-oriented cubic witness pin failed: {first}",
    )
    print(f"cell n={n} p={p} quotient={m}")
    print(f"nonnegative delta-row counterexamples: {len(witnesses)}")
    print(f"first: t={first[0]} target={first[1]} odd={first[2]} values={first[3]}")
    print("PASS: generic nonnegative-row transfer is false; any surviving implication must use rank-row structure")


if __name__ == "__main__":
    main()
