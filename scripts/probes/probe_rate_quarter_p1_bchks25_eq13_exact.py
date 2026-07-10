#!/usr/bin/env python3
"""Exact P1 optimization of BCHKS25 (ECCC TR25-169) Equation (13).

The paper's Lemma 3.1 chooses convenient, non-optimal real degree caps.  This
probe keeps the same interpolation argument but counts the integer monomials
and equations before the relaxations in (11)--(12).  It then minimizes the
strict integer firing threshold supplied by (13).

This is an optimization of the universal dimension-count proof, not a claim
that the Guruswami--Sudan system cannot have an input-dependent kernel outside
the dimension-count range.
"""

from __future__ import annotations

from fractions import Fraction


N = 2**30
K = 2**28
GAMMA_NUM = 480_946_858
AGREEMENT = N - GAMMA_NUM


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def num_variables(x_cap: int, y_cap: int, z_cap: int) -> int:
    """Monomials i+k*j<DX, j<DY, and j+h<DZ in one ceiling cell."""
    return sum(
        (x_cap - K * j) * (z_cap - j)
        for j in range(y_cap)
    )


def num_equations(multiplicity: int, z_cap: int) -> int:
    """Coefficient equations from (10), before the paper's relaxation."""
    return N * sum(
        (multiplicity - s) * max(z_cap - s, 0)
        for s in range(multiplicity)
    )


def minimum_x_cap(multiplicity: int, y_cap: int, z_cap: int) -> int:
    """Smallest ceil(DX) making the exact homogeneous system underdetermined."""
    z_sum = sum(z_cap - j for j in range(y_cap))
    weighted_j_sum = sum(j * (z_cap - j) for j in range(y_cap))
    equations = num_equations(multiplicity, z_cap)
    rank_nullity_x = (equations + K * weighted_j_sum) // z_sum + 1

    # Necessary ceiling-cell condition for some DX >= k*DY:
    # DX <= x_cap and DY > y_cap-1 imply x_cap > k*(y_cap-1).
    cap_feasibility_x = K * (y_cap - 1) + 1
    return max(rank_nullity_x, cap_feasibility_x)


def cell_infimum(x_cap: int, y_cap: int, z_cap: int) -> int:
    """Infimum of the Eq. (13) RHS over this open ceiling cell."""
    return (
        2 * (x_cap - 1) * (y_cap - 1) ** 2 * (z_cap - 1)
        + (GAMMA_NUM + 1) * (y_cap - 1)
    )


def optimize_ceiling_cells(initial_bound: int) -> tuple[tuple[int, ...], int]:
    """Exhaust every ceiling cell whose optimistic infimum can beat the incumbent.

    Paper-side cap conditions used here are

      m >= 3, DY >= m-1, DX >= k*DY, DZ >= DY,
      DX <= m*(1-gamma)*N,

    together with the exact rank-nullity count.  The P1 Johnson-gap condition
    separately forces m >= 5.
    """
    best = (initial_bound, 0, 0, 0, 0, 0)
    cells_checked = 0
    multiplicity = 5

    while True:
        # For every feasible cap, Eq. (13) is at least
        # 2*k*DY^4 + (gamma*N+1)*DY and DY >= m-1.
        multiplicity_lower_bound = (
            2 * K * (multiplicity - 1) ** 4
            + (GAMMA_NUM + 1) * (multiplicity - 1)
        )
        if multiplicity_lower_bound >= best[0]:
            break

        max_x_cap = multiplicity * AGREEMENT
        # k*(y_cap-1) < m*AGREEMENT is necessary for a feasible cap cell.
        max_y_cap = (max_x_cap - 1) // K + 1
        for y_cap in range(multiplicity - 1, max_y_cap + 1):
            z_cap = y_cap
            while True:
                # Every feasible cell has x_cap-1 >= k*(y_cap-1).
                cell_lower_bound = (
                    2 * K * (y_cap - 1) ** 3 * (z_cap - 1)
                    + (GAMMA_NUM + 1) * (y_cap - 1)
                )
                if cell_lower_bound >= best[0]:
                    break

                x_cap = minimum_x_cap(multiplicity, y_cap, z_cap)
                if x_cap <= max_x_cap:
                    variables = num_variables(x_cap, y_cap, z_cap)
                    equations = num_equations(multiplicity, z_cap)
                    assert variables > equations
                    candidate = (
                        cell_infimum(x_cap, y_cap, z_cap),
                        multiplicity,
                        x_cap,
                        y_cap,
                        z_cap,
                        variables - equations,
                    )
                    if candidate < best:
                        best = candidate
                cells_checked += 1
                z_cap += 1
        multiplicity += 1

    return best, cells_checked


def main() -> None:
    rho = Fraction(K, N)
    sqrt_rho = Fraction(1, 2)
    gamma = Fraction(GAMMA_NUM, N)
    eta = 1 - sqrt_rho - gamma
    multiplicity_ratio = sqrt_rho / (2 * eta)
    assert rho == Fraction(1, 4)
    assert eta == Fraction(27_962_027, 536_870_912)
    assert 4 < multiplicity_ratio < 5
    assert ceil_fraction(multiplicity_ratio) == 5

    print("== P1 parameters and strict multiplicity ==")
    print(f"N={N}, k={K}, gamma={gamma}, eta={eta}")
    print(
        "sqrt(rho)/(2*eta)="
        f"{multiplicity_ratio}={float(multiplicity_ratio):.12f}; ceil=5"
    )

    # The convenient caps printed in Lemma 3.1 / Theorem 1.5.
    published_dx = 11 * K
    published_dy = 11
    published_dz = Fraction(121, 3)
    published_rhs = (
        2 * published_dx * published_dy**2 * published_dz
        + (GAMMA_NUM + 1) * published_dy
    )
    headline_rhs = (
        (
            2 * Fraction(11, 2) ** 5
            + 3 * Fraction(11, 2) * gamma * rho
        )
        / (3 * rho * sqrt_rho)
        * N
        + Fraction(11, 1)
    )
    published_firing_count = published_rhs.numerator // published_rhs.denominator + 1
    assert headline_rhs == published_rhs
    assert published_rhs == Fraction(86_479_468_494_859, 3)
    assert published_firing_count == 28_826_489_498_287

    print("\n== Theorem 1.5 printed degree choice ==")
    print(
        f"DX={published_dx}, DY={published_dy}, DZ={published_dz}; "
        f"Eq13 RHS={published_rhs}"
    )
    print(f"smallest integer |S| with |S|>RHS: {published_firing_count}")

    best, cells_checked = optimize_ceiling_cells(published_firing_count)
    infimum, multiplicity, x_cap, y_cap, z_cap, margin = best
    assert best == (11_510_231_640_867, 5, 2_959_337_223, 10, 25, 155)
    assert num_variables(x_cap, y_cap, z_cap) == 381_178_347_675
    assert num_equations(multiplicity, z_cap) == 381_178_347_520

    # Exhibit actual rational caps in the minimizing open ceiling cell.  The
    # tiny epsilon makes the Eq. (13) RHS strictly between two consecutive
    # integers, resolving both strict inequalities without floating point.
    epsilon = Fraction(1, 10**18)
    dx = x_cap - 1 + epsilon
    dy = y_cap - 1 + epsilon
    dz = z_cap - 1 + epsilon
    rhs = 2 * dx * dy**2 * dz + (GAMMA_NUM + 1) * dy

    assert ceil_fraction(dx) == x_cap
    assert ceil_fraction(dy) == y_cap
    assert ceil_fraction(dz) == z_cap
    assert dy >= multiplicity - 1
    assert dx >= K * dy
    assert dz >= dy
    assert dx <= multiplicity * AGREEMENT
    assert infimum < rhs < infimum + 1

    firing_count = infimum + 1
    exceptional_cap = infimum
    assert firing_count == 11_510_231_640_868
    assert exceptional_cap > N
    assert 10_719 * N < exceptional_cap < 10_720 * N

    print("\n== Exact ceiling-cell optimization of (10)--(13) ==")
    print(f"finite cells checked: {cells_checked}")
    print(
        "best cell: "
        f"m={multiplicity}, ceil(DX)={x_cap}, ceil(DY)={y_cap}, "
        f"ceil(DZ)={z_cap}"
    )
    print(
        f"variables={num_variables(x_cap, y_cap, z_cap)}, "
        f"equations={num_equations(multiplicity, z_cap)}, margin={margin}"
    )
    print(f"explicit epsilon={epsilon}")
    print(f"caps: DX={dx}, DY={dy}, DZ={dz}")
    print(f"Eq13 RHS - infimum = {rhs - infimum}")
    print(f"{infimum} < Eq13 RHS < {infimum + 1}")
    print(f"smallest integer firing count: {firing_count}")
    print(f"contrapositive exceptional cap: {exceptional_cap}")

    print("\n== P1 comparison ==")
    print(f"target exceptional cap N={N}; trigger at pin scale N+1={N + 1}")
    print(
        f"optimized cap = 10719*N + {exceptional_cap - 10_719 * N} "
        f"(strictly between 10719*N and 10720*N)"
    )
    print(
        "headline-to-optimized cap ratio = "
        f"{float(Fraction(published_firing_count - 1, exceptional_cap)):.9f}"
    )
    assert N + 1 < firing_count
    print("N+1 does not fire Equation (13): VERIFIED")
    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main()
