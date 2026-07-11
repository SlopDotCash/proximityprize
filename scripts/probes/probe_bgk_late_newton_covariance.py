#!/usr/bin/env python3
"""PROBE: exact signed Newton-covariance decomposition at the two late steps.

This is computational reconnaissance for issue #466, not a theorem.  For the
``s``-subset sum histogram ``a_s`` of an order-``n`` subgroup ``G < F_p^*``, put

    U_j^(r)(y) = sum_(x in G) a_(r+1-j)(y-j*x),       1 <= j <= r+1.

The elementary-symmetric Newton identity is the pointwise integer identity

    (r+1) a_(r+1) = U_1 - U_2 + U_3 - ... + (-1)^r U_(r+1).

Consequently, if

    K_jk = (-1)^(j+k) (p <U_j,U_k> - mass(U_j) mass(U_k)),

then ``(r+1)^2 Delta_(r+1) = sum_(j,k) K_jk`` exactly.  Here
``Delta_s = p sum_y a_s(y)^2 - C(n,s)^2``.  The contribution of a diagonal
cell is ``n*K_jj / ((n-r)^2 Delta_r)`` and that of an unordered off-diagonal
pair is twice this quantity; their sum is the exact transition ratio

    c_r = n Z_(r+1)/Z_r.

No complex FFT or floating approximation is used.  Histograms and convolution
values are int64 after explicit size checks; all centered products and final
ratios use Python's unbounded integers and ``fractions.Fraction``.  Multiplicative
orbit compression reduces every exact inner product to the zero cell plus one
representative of each ``G``-orbit.  The full Newton identity is independently
checked against the directly computed next subset histogram.

The default cells are the two favorable n=64 cells and the counterexample from
``probe_bgk_subset_trajectory_birthday.py``.  ``--extended`` adds several exact
n=64 stress cells.  Product-unit effects are normalized separately by the live
injective gap ``135135-126871=8264`` and by the hypothetical gap
``135135-127009=8126`` if the repeated-sector reservation of 138 were returned;
no internal repeated-coordinate covariance is credited.  Decimals are only
renderings of exact rational values.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from math import comb

import numpy as np

from probe_bgk_subset_trajectory_birthday import primitive_root, torsion_subgroup


DEFAULT_CELLS = (
    ("split-64", 64, 1_000_193),
    ("edge-64", 64, 1_250_177),
    ("counter-64", 64, 750_209),
)

WICK_PRODUCT = 135_135
CURRENT_INJECTIVE_GAP = 8_264
FREE_REPEATED_RESERVATION_GAP = 8_126

EXTENDED_CELLS = (
    ("stress-355009", 64, 355_009),
    ("stress-400321", 64, 400_321),
    ("stress-421313", 64, 421_313),
    ("stress-665857", 64, 665_857),
    ("stress-697601", 64, 697_601),
)


@dataclass(frozen=True)
class OrbitProfile:
    zero: int
    nonzero_orbits: np.ndarray
    mass: int


def subset_histograms(order: int, prime: int, maximum_size: int = 7) -> list[np.ndarray]:
    """Return exact subset-sum histograms through ``maximum_size``."""
    subgroup = torsion_subgroup(order, prime)
    histograms = [np.zeros(prime, dtype=np.int64) for _ in range(maximum_size + 1)]
    histograms[0][0] = 1
    for used, element in enumerate(subgroup, start=1):
        for size in range(min(maximum_size, used), 0, -1):
            histograms[size] += np.roll(histograms[size - 1], element)
    for size, histogram in enumerate(histograms):
        assert int(histogram.sum()) == comb(order, size)
        assert int(histogram.min()) >= 0
    return histograms


def orbit_representatives(order: int, prime: int) -> np.ndarray:
    """One representative for every nonzero multiplicative ``G``-orbit."""
    index = (prime - 1) // order
    generator = primitive_root(prime)
    representatives = np.empty(index, dtype=np.int64)
    representatives[0] = 1
    for exponent in range(1, index):
        representatives[exponent] = (
            int(representatives[exponent - 1]) * generator
        ) % prime
    assert len(set(map(int, representatives))) == index
    return representatives


def newton_term_profile(
    histogram: np.ndarray,
    subgroup: tuple[int, ...],
    representatives: np.ndarray,
    multiplier: int,
) -> OrbitProfile:
    """Exact orbit-compressed physical histogram of ``p_j e_s``."""
    prime = len(histogram)
    values = np.zeros(len(representatives), dtype=np.int64)
    for element in subgroup:
        values += histogram[(representatives - multiplier * element) % prime]
    zero = sum(int(histogram[(-multiplier * element) % prime]) for element in subgroup)
    mass = zero + len(subgroup) * int(values.sum())
    expected_mass = len(subgroup) * int(histogram.sum())
    assert mass == expected_mass
    assert int(values.min()) >= 0 and zero >= 0
    return OrbitProfile(zero, values, mass)


def exact_orbit_dot(left: OrbitProfile, right: OrbitProfile, order: int) -> int:
    """Exact full-field dot product from compressed orbit profiles.

    Chunking guarantees that each NumPy dot product stays below int64 even
    though the final centered expression need not do so.
    """
    chunk_size = 2048
    result = left.zero * right.zero
    for start in range(0, len(left.nonzero_orbits), chunk_size):
        stop = min(len(left.nonzero_orbits), start + chunk_size)
        left_chunk = left.nonzero_orbits[start:stop]
        right_chunk = right.nonzero_orbits[start:stop]
        chunk_bound = len(left_chunk) * int(left_chunk.max(initial=0)) * int(
            right_chunk.max(initial=0)
        )
        assert chunk_bound < 2**63
        result += order * int(np.dot(left_chunk, right_chunk))
    return result


def centered_covariance(
    left: OrbitProfile, right: OrbitProfile, order: int, prime: int
) -> int:
    return prime * exact_orbit_dot(left, right, order) - left.mass * right.mass


def delta(histogram: np.ndarray, total: int, prime: int) -> int:
    collision = int(np.dot(histogram, histogram))
    return prime * collision - total * total


@dataclass(frozen=True)
class StepReport:
    ratio: Fraction
    diagonal: tuple[Fraction, ...]
    cross: dict[tuple[int, int], Fraction]
    raw_covariance: dict[tuple[int, int], int]


def decompose_step(
    order: int,
    prime: int,
    histograms: list[np.ndarray],
    subgroup: tuple[int, ...],
    representatives: np.ndarray,
    r: int,
) -> StepReport:
    profiles = []
    for multiplier in range(1, r + 2):
        subset_size = r + 1 - multiplier
        profiles.append(
            newton_term_profile(
                histograms[subset_size], subgroup, representatives, multiplier
            )
        )

    previous_delta = delta(histograms[r], comb(order, r), prime)
    next_delta = delta(histograms[r + 1], comb(order, r + 1), prime)
    assert previous_delta > 0 and next_delta > 0
    denominator = (order - r) ** 2 * previous_delta

    diagonal: list[Fraction] = []
    cross: dict[tuple[int, int], Fraction] = {}
    raw: dict[tuple[int, int], int] = {}
    signed_total = 0
    for j, left in enumerate(profiles, start=1):
        for k, right in enumerate(profiles, start=1):
            covariance = centered_covariance(left, right, order, prime)
            signed = covariance if (j + k) % 2 == 0 else -covariance
            signed_total += signed
            if j <= k:
                raw[(j, k)] = covariance
            if j == k:
                diagonal.append(Fraction(order * signed, denominator))
            elif j < k:
                cross[(j, k)] = Fraction(2 * order * signed, denominator)

    # This verifies orbit compression, every sign, and the physical Newton
    # expansion against the independently formed (r+1)-subset histogram.
    assert signed_total == (r + 1) ** 2 * next_delta
    ratio = Fraction(order * signed_total, denominator)
    assert ratio == sum(diagonal, start=Fraction(0)) + sum(
        cross.values(), start=Fraction(0)
    )
    return StepReport(ratio, tuple(diagonal), cross, raw)


def render_fraction(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def print_step(label: str, r: int, report: StepReport, show_exact: bool) -> None:
    wick = Fraction(2 * r + 1)
    dominant = report.cross[(1, 2)]
    leading_pair = report.diagonal[0] + report.diagonal[1] + dominant
    tail = report.ratio - leading_pair
    deficit = wick - report.ratio
    deficit_check = (
        (wick - report.diagonal[0]) - dominant - report.diagonal[1] - tail
    )
    assert deficit == deficit_check

    covariance12 = report.raw_covariance[(1, 2)]
    covariance11 = report.raw_covariance[(1, 1)]
    covariance22 = report.raw_covariance[(2, 2)]
    assert covariance11 > 0 and covariance22 > 0
    rho_squared = Fraction(covariance12**2, covariance11 * covariance22)

    # Convert a normalized c_r saving into primitive injective-product units by
    # holding the other five Wick numerators fixed.  The two denominators keep
    # the current injective reservation (8264) separate from the hypothetical
    # 8126 gap if the repeated-sector reservation of 138 were returned in full.
    product_units_per_step = Fraction(WICK_PRODUCT, wick)
    diagonal_one_product_saving = (wick - report.diagonal[0]) * product_units_per_step
    dominant_product_saving = -dominant * product_units_per_step
    lower_term_product_effect = -(report.diagonal[1] + tail) * product_units_per_step
    net_product_saving = deficit * product_units_per_step
    assert (
        diagonal_one_product_saving
        + dominant_product_saving
        + lower_term_product_effect
        == net_product_saving
    )

    print(f"  {label} c_{r}={float(report.ratio):.12f}  Wick-c={float(deficit):+.12f}")
    print(
        "    exact deficit split: "
        f"Wick-diag1={float(wick-report.diagonal[0]):+.12f}, "
        f"-(cross12)={float(-dominant):+.12f}, "
        f"-diag2={float(-report.diagonal[1]):+.12f}, "
        f"-tail={float(-tail):+.12f}"
    )
    print(
        f"    leading U1-U2={float(leading_pair):.12f}, "
        f"all j>=3 correction={float(tail):+.12f}, "
        f"rho12^2={float(rho_squared):.9f}"
    )
    product_effects = (
        diagonal_one_product_saving,
        dominant_product_saving,
        lower_term_product_effect,
        net_product_saving,
    )
    print(
        "    injective product units [diag1,cross12,lower,net]="
        + ",".join(f"{float(value):+.6f}" for value in product_effects)
    )
    print(
        "      /gap8264="
        + ",".join(
            f"{float(value/CURRENT_INJECTIVE_GAP):+.6f}" for value in product_effects
        )
        + "; /gap8126="
        + ",".join(
            f"{float(value/FREE_REPEATED_RESERVATION_GAP):+.6f}"
            for value in product_effects
        )
    )

    negative_cross = sorted(
        ((value, pair) for pair, value in report.cross.items() if value < 0)
    )
    positive_cross_sum = sum(
        (value for value in report.cross.values() if value > 0), start=Fraction(0)
    )
    negative_cross_sum = sum(
        (value for value in report.cross.values() if value < 0), start=Fraction(0)
    )
    print(
        f"    cross sums: negative={float(negative_cross_sum):+.12f}, "
        f"positive={float(positive_cross_sum):+.12f}; largest negative pairs="
        + ", ".join(
            f"{pair}:{float(value):+.9f}" for value, pair in negative_cross[:5]
        )
    )

    if show_exact:
        print(f"    ratio={render_fraction(report.ratio)}")
        print(
            "    diagonal="
            + ", ".join(
                f"{index}:{render_fraction(value)}"
                for index, value in enumerate(report.diagonal, start=1)
            )
        )
        print(
            f"    cross12={render_fraction(dominant)}; "
            f"tail={render_fraction(tail)}; rho12^2={render_fraction(rho_squared)}"
        )


def run_cell(label: str, order: int, prime: int, show_exact: bool) -> None:
    print(f"CELL {label}: n={order}, p={prime}, index={(prime-1)//order}")
    histograms = subset_histograms(order, prime)
    subgroup = torsion_subgroup(order, prime)
    representatives = orbit_representatives(order, prime)
    for r in (5, 6):
        report = decompose_step(
            order, prime, histograms, subgroup, representatives, r
        )
        print_step(label, r, report, show_exact)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--extended", action="store_true", help="add five exact n=64 stress cells"
    )
    parser.add_argument(
        "--exact", action="store_true", help="print exact rational fingerprints"
    )
    args = parser.parse_args()

    print("PROBE ONLY: exact finite cells do not prove a production inequality.")
    cells = DEFAULT_CELLS + (EXTENDED_CELLS if args.extended else ())
    for cell in cells:
        run_cell(*cell, args.exact)


if __name__ == "__main__":
    main()
