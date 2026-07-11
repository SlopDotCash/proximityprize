#!/usr/bin/env python3
"""PROBE: exact forward subset-discrepancy ratios for dyadic subgroups.

This is computational reconnaissance for issue #466, not a theorem.  For the
order-``n`` multiplicative subgroup ``G < F_p^*``, let

    a_r(y) = #{A subset G : |A| = r and sum(A) = y},
    Z_r    = sum_y (p*a_r(y) - C(n,r))^2 / C(n,r)^2,
    c_r    = n*Z_(r+1)/Z_r.

All histograms, energies, ``Z_r``, and ``c_r`` below are exact.  The displayed
decimal is only a rendering of a ``fractions.Fraction``.  Subset histograms are
formed by the usual descending-cardinality dynamic program over ``F_p``.

The marker after each ``c_r`` compares it with the robust Wick caps:

    S : c_r <= (501/500)*(2r)       (selected one-unit defect),
    O : c_r <= (501/500)*(2r+1)     (ordinary Wick cap only),
    X : c_r exceeds the ordinary cap.

``D56`` tests the distributed last-two profile

    c_5 <= (501/500)*10.5,  c_6 <= (501/500)*12.5.

Its unscaled product is 124031.25, and applying ``501/500`` at all six steps
still gives about 125527.09 < 126871.  The preset cells deliberately include
both witnesses and counterexamples.  In particular, ``--heavy`` adds a cell
with C(64,5) < p < C(64,6): the birthday crossover alone does *not* force even
an ordinary Wick bound.

Requires NumPy.  Typical run time is under five seconds; ``--heavy`` briefly
uses roughly 600 MiB at the 8,001,281-prime cell.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb, isqrt, log2, prod
from typing import Iterable

import numpy as np


ROBUST = Fraction(501, 500)
WICK = (3, 5, 7, 9, 11, 13)
DISTRIBUTED = (
    Fraction(3),
    Fraction(5),
    Fraction(7),
    Fraction(9),
    Fraction(21, 2),
    Fraction(25, 2),
)

# (label, n, p).  These are proper subgroups; no p = n+1 full-group cell.
PRESETS = (
    ("direct-16", 16, 8209),
    ("thin-16", 16, 65537),
    ("early-dense-32", 32, 32801),
    ("split-32", 32, 300193),
    ("thin-32", 32, 1048609),
    ("split-64", 64, 1000193),
    ("edge-64", 64, 1250177),
    ("counter-64", 64, 750209),
)

HEAVY_PRESETS = (("crossover-64", 64, 8001281),)


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    for divisor in range(3, isqrt(value) + 1, 2):
        if value % divisor == 0:
            return False
    return True


def distinct_prime_factors(value: int) -> list[int]:
    factors: list[int] = []
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            factors.append(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor += 1
    if value > 1:
        factors.append(value)
    return factors


def primitive_root(prime: int) -> int:
    factors = distinct_prime_factors(prime - 1)
    for candidate in range(2, prime):
        if all(pow(candidate, (prime - 1) // factor, prime) != 1
               for factor in factors):
            return candidate
    raise AssertionError(f"no primitive root modulo {prime}")


def valuation_two(value: int) -> int:
    valuation = 0
    while value % 2 == 0:
        valuation += 1
        value //= 2
    return valuation


def torsion_subgroup(order: int, prime: int) -> tuple[int, ...]:
    assert is_prime(prime)
    assert (prime - 1) % order == 0
    generator = primitive_root(prime)
    root = pow(generator, (prime - 1) // order, prime)
    subgroup = tuple(pow(root, exponent, prime) for exponent in range(order))
    assert len(set(subgroup)) == order
    assert pow(root, order, prime) == 1
    if order > 1:
        assert pow(root, order // 2, prime) != 1
    return subgroup


def exact_trajectory(order: int, prime: int) -> tuple[list[Fraction], list[Fraction]]:
    """Return ``Z_1,...,Z_7`` and ``c_1,...,c_6`` exactly."""
    subgroup = torsion_subgroup(order, prime)
    maximum_total = comb(order, 7)
    assert maximum_total**2 < 2**63, "int64 collision sum is not certified safe"

    histograms = [np.zeros(prime, dtype=np.int64) for _ in range(8)]
    histograms[0][0] = 1
    for used, element in enumerate(subgroup, start=1):
        for size in range(min(7, used), 0, -1):
            histograms[size] += np.roll(histograms[size - 1], element)

    deviations: list[Fraction] = []
    for size in range(1, 8):
        total = comb(order, size)
        assert int(histograms[size].sum()) == total
        collision = int(np.dot(histograms[size], histograms[size]))
        centered_collision = prime * collision - total**2
        assert centered_collision >= 0
        deviations.append(Fraction(prime * centered_collision, total**2))

    assert all(value > 0 for value in deviations)
    ratios = [Fraction(order) * deviations[size] / deviations[size - 1]
              for size in range(1, 7)]
    return deviations, ratios


def cap_marker(step: int, ratio: Fraction) -> str:
    selected = ROBUST * (WICK[step - 1] - 1)
    ordinary = ROBUST * WICK[step - 1]
    if ratio <= selected:
        return "S"
    if ratio <= ordinary:
        return "O"
    return "X"


def distributed_last_two(ratios: list[Fraction]) -> bool:
    return (ratios[4] <= ROBUST * DISTRIBUTED[4]
            and ratios[5] <= ROBUST * DISTRIBUTED[5])


def distributed_all(ratios: list[Fraction]) -> bool:
    return all(ratio <= ROBUST * cap
               for ratio, cap in zip(ratios, DISTRIBUTED, strict=True))


def distributed_tail(ratios: list[Fraction]) -> bool:
    """The production-relevant later-step test, omitting the known finite-n c1 excess."""
    return all(ratio <= ROBUST * DISTRIBUTED[step]
               for step, ratio in enumerate(ratios[1:], start=1))


def production_birthday_report() -> None:
    order = 2**30
    prime = order * (2**128 + 192) + 1
    counts = [comb(order, size) for size in range(1, 8)]

    # Exact integer windows, not decimal guesses.
    assert 30720 * counts[4] < prime < 30721 * counts[4]
    assert 5825 * prime < counts[5] < 5826 * prime
    assert Fraction(counts[5], counts[4]) == Fraction(order - 5, 6)

    print("PRODUCTION BIRTHDAY LOADS (exact integers, decimals shown)")
    for size, count in enumerate(counts, start=1):
        load = Fraction(count, prime)
        print(f"  r={size}: C(n,r)/p={float(load):.12g}  "
              f"log2={log2(float(load)):.6f}")
    print("  exact windows: 30720*C(n,5) < p < 30721*C(n,5);")
    print("                 5825*p < C(n,6) < 5826*p")
    print(f"  load jump L6/L5=(n-5)/6={float(Fraction(order - 5, 6)):.6f}\n")


def run_cells(cells: Iterable[tuple[str, int, int]], show_exact: bool) -> None:
    results: list[tuple[str, int, int, list[Fraction]]] = []
    print("EXACT FINITE-FIELD CELLS")
    print("  marker S=selected robust, O=ordinary robust, X=above ordinary")
    print("  label             n         p    v2(index)       L5       L6       L7"
          "       c1       c2       c3       c4       c5       c6  D56  product")
    for label, order, prime in cells:
        _, ratios = exact_trajectory(order, prime)
        results.append((label, order, prime, ratios))
        index = (prime - 1) // order
        loads = [Fraction(comb(order, size), prime) for size in (5, 6, 7)]
        rendered = " ".join(
            f"{float(ratio):7.3f}{cap_marker(step, ratio)}"
            for step, ratio in enumerate(ratios, start=1)
        )
        product_exact = prod(ratios, start=Fraction(1))
        print(f"  {label:16s} {order:3d} {prime:9d} {valuation_two(index):12d} "
              f"{float(loads[0]):8.3g} {float(loads[1]):8.3g} {float(loads[2]):8.3g} "
              f"{rendered}   {'Y' if distributed_last_two(ratios) else '-'}   "
              f"{float(product_exact):9.1f}{'*' if product_exact < 126871 else ' '}")

    print("  * product c1...c6 < 126871 in this finite cell")
    print("  D56 is only the last-two test; the full distributed profile is reported below.")
    for label, _order, _prime, ratios in results:
        print(f"    {label:16s}: distributed-r2..r6="
              f"{'Y' if distributed_tail(ratios) else '-'}; "
              f"distributed-all={'Y' if distributed_all(ratios) else '-'}")

    pass_counts = []
    for step in range(2, 7):
        count = sum(ratios[step - 1] <= ROBUST * (WICK[step - 1] - 1)
                    for _label, _order, _prime, ratios in results)
        pass_counts.append((count, step))
    ranking = sorted(pass_counts, key=lambda item: (-item[0], -item[1]))
    print("  preset selected-cap counts (reconnaissance, not statistics): "
          + ", ".join(f"r={step}: {count}/{len(results)}" for count, step in ranking))

    if show_exact:
        print("\nEXACT RATIO FINGERPRINTS")
        for label, order, prime, ratios in results:
            print(f"  {label} (n={order}, p={prime})")
            for step, ratio in enumerate(ratios, start=1):
                print(f"    c_{step} = {ratio.numerator}/{ratio.denominator}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--heavy", action="store_true",
                        help="include the 8,001,281-prime direct-crossover cell")
    parser.add_argument("--exact", action="store_true",
                        help="print numerator/denominator fingerprints for every c_r")
    args = parser.parse_args()

    # The distributed arithmetic is itself exact and independent of the probe.
    distributed_product = Fraction(1)
    for cap in DISTRIBUTED:
        distributed_product *= cap
    robust_product = ROBUST**6 * distributed_product
    assert distributed_product == Fraction(496125, 4)
    assert robust_product < 126871
    print("PROBE ONLY: finite fields do not prove the production inequality.")
    print(f"distributed product={float(distributed_product):.6f}; "
          f"robust product={float(robust_product):.6f} < 126871\n")

    production_birthday_report()
    cells = PRESETS + (HEAVY_PRESETS if args.heavy else ())
    run_cells(cells, args.exact)


if __name__ == "__main__":
    main()
