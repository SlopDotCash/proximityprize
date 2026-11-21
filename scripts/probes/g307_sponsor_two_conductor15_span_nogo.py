#!/usr/bin/env python3
"""Exact sponsor-two conductor-15 weighted-kernel no-go.

For each exact circuit cell this script computes the coefficient-two target and the complete
quotient-generator-invariant trace coordinates (P,L3,L5,L15), then verifies the positive Farkas
relation used by G307. Arithmetic is integer-only; no FFT, floating point, fitting, or LP solver
is used in the reproducibility path.
"""
from __future__ import annotations

import importlib.util
from math import gcd
from pathlib import Path

BASE = Path(__file__).with_name("g302_common_order7_normal_nogo.py")
SPEC = importlib.util.spec_from_file_location("g302_base", BASE)
BASE_MODULE = importlib.util.module_from_spec(SPEC)
if SPEC.loader is None:
    raise ImportError(f"could not load shared exact arithmetic helper from {BASE}")
SPEC.loader.exec_module(BASE_MODULE)


def require(condition: bool, message: str) -> None:
    """Keep the G307 exact circuit certificate active under Python optimization."""
    if not condition:
        raise AssertionError(message)


def ramanujan_three(j: int) -> int:
    return 2 if j % 3 == 0 else -1


def ramanujan_five(j: int) -> int:
    return 4 if j % 5 == 0 else -1


def ramanujan_fifteen(j: int) -> int:
    # Ramanujan sums are multiplicative in coprime conductors.
    return ramanujan_three(j) * ramanujan_five(j)


def run_cell(n: int, p: int, r: int) -> tuple[int, tuple[int, int, int, int]]:
    primitive = BASE_MODULE.primitive_root(p)
    quotient_order = (p - 1) // n
    group = BASE_MODULE.subgroup(p, n, primitive)
    require(quotient_order % 15 == 0, f"quotient order {quotient_order} is not divisible by 15")
    require(pow(2, n, p) != 1, f"coefficient 2 is degenerate in G at p={p}, n={n}")
    histogram = BASE_MODULE.subset_hist(group, p, 6)
    row = BASE_MODULE.difference_corr(histogram[r], histogram[r - 1], p)
    representatives = [pow(primitive, j, p) for j in range(quotient_order)]
    values = [
        BASE_MODULE.alignment(BASE_MODULE.weighted_kernel(group, p, coefficient), row, p, n)
        for coefficient in representatives
    ]
    target = BASE_MODULE.alignment(BASE_MODULE.weighted_kernel(group, p, 2), row, p, n)
    features = (
        sum(values),
        sum(ramanujan_three(j) * values[j] for j in range(quotient_order)),
        sum(ramanujan_five(j) * values[j] for j in range(quotient_order)),
        sum(ramanujan_fifteen(j) * values[j] for j in range(quotient_order)),
    )
    # Every trace is independent of the cyclic quotient generator.
    for unit in range(1, quotient_order):
        if gcd(unit, quotient_order) == 1:
            changed = (
                sum(values[(unit * j) % quotient_order] for j in range(quotient_order)),
                sum(ramanujan_three(j) * values[(unit * j) % quotient_order]
                    for j in range(quotient_order)),
                sum(ramanujan_five(j) * values[(unit * j) % quotient_order]
                    for j in range(quotient_order)),
                sum(ramanujan_fifteen(j) * values[(unit * j) % quotient_order]
                    for j in range(quotient_order)),
            )
            require(
                changed == features,
                f"G307 trace coordinates depend on quotient generator unit={unit} at p={p}",
            )
    return target, features


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def main() -> None:
    sponsor_one = 2**128 + 192
    sponsor_two = 2**129 + 13
    require(sponsor_two % 75 == 0, "sponsor two is not divisible by the 75-quotient requirement")
    require(sponsor_one % 5 != 0, "sponsor one unexpectedly admits conductor five")

    cells = [
        (8, 241, 30, 5, 177136, (-134448, -1688928, 888808, -4046872)),
        (8, 601, 75, 5, 681872, (-382128, -2971344, -10164112, -1043336)),
        (8, 601, 75, 6, 303520, (-189392, -1149112, -4500288, -389448)),
        (16, 241, 15, 5, -936608, (-1509408, -9786528, -11055152, -25013872)),
        (16, 2161, 135, 6, 167714720,
         (-380423760, 20338363872, -568602320, -689514592)),
    ]
    circuit = [
        8238733293377050110946,
        754877671516756422812,
        3385823540912886383052,
        1425371395806543001161,
        299870825764606156,
    ]

    oriented = []
    for n, p, quotient_order, r, expected_target, expected_features in cells:
        require(quotient_order == (p - 1) // n, f"recorded quotient order changed at p={p}, n={n}")
        target, features = run_cell(n, p, r)
        require(
            target == expected_target,
            f"G307 exact target pin failed at p={p}, n={n}, r={r}: {target}",
        )
        require(
            features == expected_features,
            f"G307 exact trace feature pin failed at p={p}, n={n}, r={r}: {features}",
        )
        row = tuple(sign(target) * coordinate for coordinate in features)
        oriented.append(row)
        print(f"n={n} p={p} m={quotient_order} r={r} target={target:+d} "
              f"features={features} oriented={row}")

    for coordinate in range(4):
        total = sum(circuit[index] * oriented[index][coordinate] for index in range(5))
        require(total == 0, f"G307 positive circuit coordinate {coordinate} is {total}, expected zero")
        print(f"circuit coordinate {coordinate}: {total}")
    require(all(weight > 0 for weight in circuit), "G307 separating-circuit weights must be positive")
    require({cell[3] for cell in cells} == {5, 6}, "G307 circuit cells must cover ranks five and six")
    print("PASS: the exact positive circuit forbids every fixed separator in (P,L3,L5,L15).")


if __name__ == "__main__":
    main()
