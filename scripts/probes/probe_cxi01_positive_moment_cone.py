#!/usr/bin/env python3
"""Exact probe for the positive-matching-moment cone in #466/#505.

The G123/G124 descent matrix has rows m=1..r and depth columns s=0..r,
with entry (r-s)_m (falling factorial).  This script checks, using only
integer arithmetic, that the full-depth column s=r is zero while the other
r columns form a triangular matrix with determinant product_{j=1}^r j!.

Consequently the common nonnegative recession cone is exactly the ray e_r:
all positive matching moments determine/constrain shallow directions, but no
positive-moment LP, SOS polynomial with zero constant term, or rational dual
combination sees added mass at the fully-disjoint atom.
"""

from fractions import Fraction
from math import factorial, log


def falling(n: int, m: int) -> int:
    out = 1
    for j in range(m):
        out *= n - j
    return out


def shannon_two_atom(zero_mass: int) -> float:
    """Entropy of (zero_mass * delta_0 + delta_1)/(zero_mass+1)."""
    total = zero_mass + 1
    probs = (Fraction(zero_mass, total), Fraction(1, total))
    return -sum(float(p) * log(float(p)) for p in probs if p)


def audit(r: int) -> None:
    # Rows m=1..r; depth columns s=0..r.
    matrix = [[falling(r - s, m) for s in range(r + 1)] for m in range(1, r + 1)]
    full_depth_zero = all(row[r] == 0 for row in matrix)

    # Re-index shallow columns by t=r-s in ascending order.  Entry (m,t)
    # is (t)_m, hence zero below the diagonal and m! on the diagonal.
    triangular = [[falling(t, m) for t in range(1, r + 1)] for m in range(1, r + 1)]
    upper_triangular = all(triangular[m - 1][t - 1] == 0
                           for m in range(1, r + 1)
                           for t in range(1, m))
    diagonal = [triangular[m - 1][m - 1] for m in range(1, r + 1)]
    expected_diagonal = [factorial(m) for m in range(1, r + 1)]
    determinant = 1
    for value in diagonal:
        determinant *= value

    assert full_depth_zero
    assert upper_triangular
    assert diagonal == expected_diagonal
    assert determinant > 0

    print(
        f"r={r:3d} rows={r:3d} cols={r + 1:3d} "
        f"rank={r:3d} nullity=1 full_depth_column=ZERO "
        f"det_bits={determinant.bit_length()}"
    )


def main() -> None:
    print("CXI01 exact positive-moment cone audit")
    for r in (1, 2, 3, 4, 5, 8, 16, 32, 110):
        audit(r)

    print("\nDual full-depth column for rows m=0..8:")
    print([falling(0, m) for m in range(9)])
    print("Any dual certificate with target coefficient c_r>0 therefore needs lambda_0>0.")
    print("Row m=0 is total mass E_r, so that certificate is circular at the open rung.")

    print("\nTruncated-moment / maximum-entropy stress test:")
    for zero_mass in (1, 10, 10**3, 10**6):
        # For mu_T = T delta_0 + delta_1, every positive falling-factorial
        # moment is independent of T: first moment 1, all higher moments 0.
        moments = [zero_mass + 1] + [1] + [0] * 5
        print(
            f"T={zero_mass:7d} moments_m0..6={moments} "
            f"normalized_atom0={zero_mass / (zero_mass + 1):.9f} "
            f"entropy={shannon_two_atom(zero_mass):.12f}"
        )

    print("\nVERDICT: exact common null ray e_r; positive descent moments alone cannot bound full depth.")


if __name__ == "__main__":
    main()
