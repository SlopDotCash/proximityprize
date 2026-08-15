#!/usr/bin/env python3
"""PROBE: exact finite-field reconnaissance for the late Newton C12 alignment.

For a multiplicative subgroup ``G < F_p^*`` of order ``n`` and ``r in {5,6}``,
let

    W(t) = #{(x,y) in G^2 : 2*y-x=t},
    R_r(t) = #{(S,T) : |S|=r, |T|=r-1, sum(S)-sum(T)=t}.

The physical Newton cross collision and its centered alignment are

    C12 = sum_t W(t) R_r(t),
    A_r = p*C12 - n^2*C(n,r)*C(n,r-1).

This script computes every quantity with integer arithmetic.  Subset-sum
histograms use descending-cardinality dynamic programming.  Multiplication by
``G`` leaves both rows invariant, so ``R_r`` is evaluated only at one
representative of each nonzero ``G``-orbit; the exact row mass certifies the
compression.  Small cells additionally form the complete ``R_r`` row and
cross-check the factorized count against a separately constructed pair of
Newton histograms.

The normalized dominant-pair energy is

    d_r = n * [p*(C11+C22-2*C12)-dc^2] / ((n-r)^2*Delta_r),

where ``dc=n*(C(n,r)-C(n,r-1))`` and
``Delta_r=p*sum a_r^2-C(n,r)^2``.  Thus the production-shaped targets are
``d_5 <= 10.5`` and ``d_6 <= 12.5``.  These small-field cells are discovery
and falsification tests only; no production extrapolation is made.  Printed
decimals are renderings of exact ``fractions.Fraction`` values.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import comb

import numpy as np

from probe_bgk_subset_trajectory_birthday import primitive_root, torsion_subgroup


# Nested subgroups at p=193 separate subgroup order from the ambient field.
# The remaining cells vary the quotient index while keeping all orbit
# correlations cheap enough to evaluate exactly.
CELLS = (
    ("nested-8", 8, 193),
    ("nested-16", 16, 193),
    ("nested-32", 32, 193),
    ("nested-64", 64, 193),
    ("fermat-8", 8, 17),
    ("fermat-16", 16, 257),
    ("fermat-32", 32, 257),
    ("dense-8", 8, 41),
    ("mid-8", 8, 233),
    ("thin-8", 8, 409),
    ("dense-16", 16, 97),
    ("mid-16", 16, 401),
    ("thin-16", 16, 1009),
    ("dense-32", 32, 97),
    ("mid-32", 32, 673),
    ("thin-32", 32, 2017),
    ("dense-64", 64, 257),
    ("mid-64", 64, 1601),
    ("thin-64", 64, 6529),
)

THRESHOLDS = {5: Fraction(21, 2), 6: Fraction(25, 2)}


def exact_dot(left: np.ndarray, right: np.ndarray) -> int:
    """An exact dot product with an explicit signed-int64 overflow guard."""
    assert left.shape == right.shape
    if not len(left):
        return 0
    maximum_product = int(left.max(initial=0)) * int(right.max(initial=0))
    if maximum_product == 0:
        return 0
    if maximum_product >= 2**63:
        return sum(int(x) * int(y) for x, y in zip(left, right, strict=True))
    chunk_size = max(1, min(8192, (2**63 - 1) // maximum_product))
    total = 0
    for start in range(0, len(left), chunk_size):
        stop = min(len(left), start + chunk_size)
        left_chunk = left[start:stop]
        right_chunk = right[start:stop]
        bound = len(left_chunk) * int(left_chunk.max(initial=0)) * int(
            right_chunk.max(initial=0)
        )
        assert bound < 2**63
        total += int(np.dot(left_chunk, right_chunk))
    return total


def subset_histograms(
    subgroup: tuple[int, ...], prime: int, maximum_size: int = 6
) -> list[np.ndarray]:
    """Exact subset-sum histograms ``a_0,...,a_maximum_size``."""
    histograms = [np.zeros(prime, dtype=np.int64) for _ in range(maximum_size + 1)]
    histograms[0][0] = 1
    for used, element in enumerate(subgroup, start=1):
        for size in range(min(maximum_size, used), 0, -1):
            histograms[size] += np.roll(histograms[size - 1], element)
    order = len(subgroup)
    for size, histogram in enumerate(histograms):
        assert int(histogram.min()) >= 0
        assert int(histogram.sum()) == comb(order, size)
    return histograms


def orbit_representatives(order: int, prime: int) -> np.ndarray:
    """Representatives ``1,g,...,g^(index-1)`` for the nonzero G-orbits."""
    index = (prime - 1) // order
    generator = primitive_root(prime)
    representatives = np.empty(index, dtype=np.int64)
    value = 1
    for exponent in range(index):
        representatives[exponent] = value
        value = value * generator % prime
    assert len(set(map(int, representatives))) == index
    return representatives


def marked_row(subgroup: tuple[int, ...], prime: int) -> np.ndarray:
    """The complete exact row ``W(t)=#{(x,y):2y-x=t}``."""
    row = np.zeros(prime, dtype=np.int64)
    for x in subgroup:
        for y in subgroup:
            row[(2 * y - x) % prime] += 1
    order = len(subgroup)
    assert int(row.sum()) == order**2
    return row


def difference_value(left: np.ndarray, right: np.ndarray, shift: int) -> int:
    """Return ``sum_s left(s)*right(s-shift)`` exactly."""
    return exact_dot(left, np.roll(right, shift))


@dataclass(frozen=True)
class OrbitRow:
    zero: int
    values: tuple[int, ...]
    mass: int
    square_mass: int


def difference_orbit_row(
    left: np.ndarray,
    right: np.ndarray,
    representatives: np.ndarray,
    order: int,
) -> OrbitRow:
    """Orbit-compressed adjacent subset-difference row."""
    zero = difference_value(left, right, 0)
    values = tuple(
        difference_value(left, right, int(representative))
        for representative in representatives
    )
    mass = zero + order * sum(values)
    square_mass = zero**2 + order * sum(value**2 for value in values)
    return OrbitRow(zero, values, mass, square_mass)


def newton_histogram(
    histogram: np.ndarray, subgroup: tuple[int, ...], multiplier: int
) -> np.ndarray:
    """Physical histogram ``U_j(y)=sum_x a(y-j*x)``."""
    result = np.zeros_like(histogram)
    for element in subgroup:
        result += np.roll(histogram, multiplier * element)
    return result


@dataclass(frozen=True)
class StepResult:
    r: int
    alignment: int
    mean_product: int
    c12: int
    dominant_ratio: Fraction
    gate_slack: Fraction
    signed_rho_squared: Fraction
    local_negative_orbits: int
    local_positive_orbits: int
    discordant_pairs: int
    concordant_pairs: int
    ordering_witness: tuple[int, int, int, int, int, int] | None
    marked_distribution: tuple[tuple[int, int], ...]
    r_min: int
    r_max: int


def ordering_statistics(
    marked_values: tuple[int, ...], difference_values: tuple[int, ...]
) -> tuple[int, int, tuple[int, int, int, int, int, int] | None]:
    """Count exact strict concordances/discordances among nonzero orbits."""
    discordant = 0
    concordant = 0
    witness = None
    for i in range(len(marked_values)):
        for j in range(i + 1, len(marked_values)):
            product = (marked_values[i] - marked_values[j]) * (
                difference_values[i] - difference_values[j]
            )
            if product < 0:
                discordant += 1
                if witness is None:
                    witness = (
                        i,
                        j,
                        marked_values[i],
                        marked_values[j],
                        difference_values[i],
                        difference_values[j],
                    )
            elif product > 0:
                concordant += 1
    return discordant, concordant, witness


def full_row_crosscheck(
    left: np.ndarray,
    right: np.ndarray,
    orbit_row: OrbitRow,
    representatives: np.ndarray,
    subgroup: tuple[int, ...],
    marked: np.ndarray,
    expected_c12: int,
) -> None:
    """Independently form all R(t) on designated small cells."""
    prime = len(left)
    full = np.array(
        [difference_value(left, right, shift) for shift in range(prime)],
        dtype=np.int64,
    )
    assert int(full.sum()) == orbit_row.mass
    assert exact_dot(full, full) == orbit_row.square_mass
    assert exact_dot(marked, full) == expected_c12
    assert int(full[0]) == orbit_row.zero
    for representative, expected in zip(
        representatives, orbit_row.values, strict=True
    ):
        for element in subgroup:
            assert int(full[int(representative) * element % prime]) == expected


def analyze_step(
    order: int,
    prime: int,
    subgroup: tuple[int, ...],
    representatives: np.ndarray,
    histograms: list[np.ndarray],
    marked: np.ndarray,
    r: int,
    full_check: bool,
) -> StepResult:
    """Compute and mutually certify every exact quantity for one late step."""
    left = histograms[r]
    right = histograms[r - 1]
    row = difference_orbit_row(left, right, representatives, order)
    expected_mass = comb(order, r) * comb(order, r - 1)
    assert row.mass == expected_mass

    marked_zero = int(marked[0])
    marked_values = tuple(int(marked[int(t)]) for t in representatives)
    assert marked_zero + order * sum(marked_values) == order**2
    marked_square_mass = marked_zero**2 + order * sum(value**2 for value in marked_values)
    assert marked_square_mass == exact_dot(marked, marked)

    c12_factorized = marked_zero * row.zero + order * sum(
        w * value for w, value in zip(marked_values, row.values, strict=True)
    )
    u1 = newton_histogram(left, subgroup, 1)
    u2 = newton_histogram(right, subgroup, 2)
    c11 = exact_dot(u1, u1)
    c22 = exact_dot(u2, u2)
    c12_direct = exact_dot(u1, u2)
    assert c12_factorized == c12_direct

    if full_check:
        full_row_crosscheck(
            left,
            right,
            row,
            representatives,
            subgroup,
            marked,
            c12_direct,
        )

    mean_product = order**2 * expected_mass
    alignment = prime * c12_direct - mean_product
    delta = prime * exact_dot(left, left) - comb(order, r) ** 2
    assert delta > 0
    dc = order * (comb(order, r) - comb(order, r - 1))
    dominant_energy = prime * (c11 + c22 - 2 * c12_direct) - dc**2
    assert dominant_energy >= 0
    denominator = (order - r) ** 2 * delta
    dominant_ratio = Fraction(order * dominant_energy, denominator)
    threshold = THRESHOLDS[r]
    gate_slack = threshold - dominant_ratio

    # Verify the equivalent centered-alignment lower bound exactly.
    baseline_without_alignment = prime * (c11 + c22) - dc**2 - 2 * mean_product
    required_alignment = Fraction(
        order * baseline_without_alignment - threshold * denominator,
        2 * order,
    )
    assert Fraction(alignment) - required_alignment == Fraction(
        denominator, 2 * order
    ) * gate_slack

    marked_energy = prime * marked_square_mass - order**4
    row_energy = prime * row.square_mass - expected_mass**2
    assert marked_energy >= 0 and row_energy >= 0
    if marked_energy == 0 or row_energy == 0:
        signed_rho_squared = Fraction(0)
    else:
        signed_rho_squared = Fraction(alignment**2, marked_energy * row_energy)
        if alignment < 0:
            signed_rho_squared = -signed_rho_squared
        assert abs(signed_rho_squared) <= 1

    local_negative = 0
    local_positive = 0
    centered_pairs = [(marked_zero, row.zero)] + list(
        zip(marked_values, row.values, strict=True)
    )
    for marked_value, row_value in centered_pairs:
        local_product = (prime * marked_value - order**2) * (
            prime * row_value - expected_mass
        )
        if local_product < 0:
            local_negative += 1
        elif local_product > 0:
            local_positive += 1

    discordant, concordant, witness = ordering_statistics(marked_values, row.values)
    marked_distribution = tuple(sorted(Counter(marked_values).items()))
    return StepResult(
        r=r,
        alignment=alignment,
        mean_product=mean_product,
        c12=c12_direct,
        dominant_ratio=dominant_ratio,
        gate_slack=gate_slack,
        signed_rho_squared=signed_rho_squared,
        local_negative_orbits=local_negative,
        local_positive_orbits=local_positive,
        discordant_pairs=discordant,
        concordant_pairs=concordant,
        ordering_witness=witness,
        marked_distribution=marked_distribution,
        r_min=min((row.zero, *row.values)),
        r_max=max((row.zero, *row.values)),
    )


def format_signed_fraction(value: Fraction, digits: int = 6) -> str:
    return f"{float(value):+.{digits}f}"


def main() -> None:
    print("PROBE ONLY: exact small fields do not prove a production inequality.")
    print("A=p*C12-n^2*C(n,r)C(n,r-1); rho2 is signed exact rho^2.")
    print("gate columns test d5<=10.5 and d6<=12.5; decimals render Fractions.\n")
    print(
        "label          n     p index  2inG "
        "       A5/mean      rho2_5       d5   gate "
        "       A6/mean      rho2_6       d6   gate"
    )

    records: list[tuple[str, int, int, bool, StepResult, StepResult]] = []
    for label, order, prime in CELLS:
        subgroup = torsion_subgroup(order, prime)
        representatives = orbit_representatives(order, prime)
        histograms = subset_histograms(subgroup, prime)
        marked = marked_row(subgroup, prime)
        # Full p-shift reconstruction is deliberately independent and cheap on
        # the nested/dense cells; all other cells retain the direct U1/U2 check.
        full_check = prime <= 257
        step5 = analyze_step(
            order,
            prime,
            subgroup,
            representatives,
            histograms,
            marked,
            5,
            full_check,
        )
        step6 = analyze_step(
            order,
            prime,
            subgroup,
            representatives,
            histograms,
            marked,
            6,
            full_check,
        )
        two_in_g = 2 in subgroup
        records.append((label, order, prime, two_in_g, step5, step6))
        print(
            f"{label:13s} {order:3d} {prime:5d} {(prime-1)//order:5d} "
            f"  {'Y' if two_in_g else '-'}   "
            f"{float(Fraction(step5.alignment, step5.mean_product)):+12.6e} "
            f"{format_signed_fraction(step5.signed_rho_squared):>11s} "
            f"{float(step5.dominant_ratio):8.4f} "
            f" {'Y' if step5.gate_slack >= 0 else '-'}   "
            f"{float(Fraction(step6.alignment, step6.mean_product)):+12.6e} "
            f"{format_signed_fraction(step6.signed_rho_squared):>11s} "
            f"{float(step6.dominant_ratio):8.4f} "
            f" {'Y' if step6.gate_slack >= 0 else '-'}"
        )

    print("\nORBIT/ORDERING FALSIFICATION SUMMARY")
    for label, order, prime, _two_in_g, step5, step6 in records:
        rendered = []
        for result in (step5, step6):
            rendered.append(
                f"r{result.r}:local-/+={result.local_negative_orbits}/"
                f"{result.local_positive_orbits},discord/concord="
                f"{result.discordant_pairs}/{result.concordant_pairs},"
                f"R=[{result.r_min},{result.r_max}]"
            )
        print(f"  {label:13s} n={order:2d} p={prime:4d}: " + "; ".join(rendered))

    all_steps = [
        (label, order, prime, two_in_g, result)
        for label, order, prime, two_in_g, step5, step6 in records
        for result in (step5, step6)
    ]
    negative = [record for record in all_steps if record[4].alignment < 0]
    nonnegative = [record for record in all_steps if record[4].alignment >= 0]
    gate_failures = [record for record in all_steps if record[4].gate_slack < 0]
    inversions = [record for record in all_steps if record[4].ordering_witness is not None]
    local_sign_failures = [
        record for record in all_steps if record[4].local_negative_orbits > 0
    ]
    two_in_g_steps = [record for record in all_steps if record[3]]

    print("\nEXACT NO-GO / EXTREMAL WITNESSES")
    print(
        f"  A_r>=0: negatives={len(negative)}/{len(all_steps)}, "
        f"nonnegative={len(nonnegative)}/{len(all_steps)}"
    )
    for label, order, prime, two_in_g, result in negative[:4]:
        print(
            f"    negative {label} r={result.r}: n={order},p={prime},"
            f"2inG={two_in_g}, A={result.alignment}, "
            f"A/mean={Fraction(result.alignment, result.mean_product)}"
        )
    quadrants = Counter(
        ("A+" if result.alignment >= 0 else "A-", "gate+" if result.gate_slack >= 0 else "gate-")
        for _label, _order, _prime, _two_in_g, result in all_steps
    )
    print(
        "  alignment-sign/gate quadrants: "
        + ", ".join(
            f"{alignment}/{gate}={quadrants[(alignment, gate)]}"
            for alignment in ("A+", "A-")
            for gate in ("gate+", "gate-")
        )
    )
    print(
        "  2inG (equivalently W(0)=n) does not fix sign: "
        f"negative={sum(result.alignment < 0 for *_, result in two_in_g_steps)}/"
        f"{len(two_in_g_steps)}"
    )
    print(
        f"  production-shaped gate failures={len(gate_failures)}/{len(all_steps)}"
    )
    for label, order, prime, _two_in_g, result in gate_failures[:4]:
        print(
            f"    fail {label} r={result.r}: d="
            f"{result.dominant_ratio.numerator}/{result.dominant_ratio.denominator}, "
            f"threshold={THRESHOLDS[result.r]}"
        )
    print(
        f"  strict comonotonicity: inversion witnesses={len(inversions)}/{len(all_steps)}"
    )
    for label, order, prime, _two_in_g, result in inversions[:4]:
        assert result.ordering_witness is not None
        i, j, wi, wj, ri, rj = result.ordering_witness
        print(
            f"    inversion {label} r={result.r}: orbit#{i}/#{j}, "
            f"W={wi}/{wj}, R={ri}/{rj}"
        )
    print(
        "  pointwise centered-product positivity: negative orbit present="
        f"{len(local_sign_failures)}/{len(all_steps)}"
    )

    minimum = min(
        all_steps,
        key=lambda record: Fraction(record[4].alignment, record[4].mean_product),
    )
    maximum = max(
        all_steps,
        key=lambda record: Fraction(record[4].alignment, record[4].mean_product),
    )
    print("\nEXTREMA (exact fingerprints)")
    for name, record in (("minimum", minimum), ("maximum", maximum)):
        label, order, prime, two_in_g, result = record
        print(
            f"  {name}: {label} r={result.r}, n={order}, p={prime}, 2inG={two_in_g}, "
            f"A={result.alignment}, A/mean="
            f"{Fraction(result.alignment, result.mean_product)}, "
            f"rho2={result.signed_rho_squared}, d={result.dominant_ratio}, "
            f"gate_slack={result.gate_slack}"
        )
        print(
            "    nonzero-orbit W distribution="
            + ",".join(f"{value}:{count}" for value, count in result.marked_distribution)
        )

    print("\nCHECKS")
    print(
        "  every cell: subgroup/primality, subset masses, W/R orbit masses, "
        "C12 direct=factorized, centered gate equivalence"
    )
    print("  p<=257 cells: complete R row, full orbit invariance, full dot=factorized")
    print("  conclusion: finite reconnaissance only; no production extrapolation")


if __name__ == "__main__":
    main()
