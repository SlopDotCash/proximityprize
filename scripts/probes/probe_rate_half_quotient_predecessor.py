#!/usr/bin/env python3
"""Exact toy audit of the rate-half quotient predecessor.

The production obstruction in ``_PrizeShapeRateHalfBracket.lean`` uses

    n = 64*m, k = 32*m, agreement = 33*m

and leaves the immediately preceding error radius, whose agreement is
``33*m + 1``.  The smallest nontrivial lift with the same geometry is

    RS[16, 8], quotient (s,m,r) = (8,2,5),
    boundary agreement 10, predecessor agreement 11.

This probe works over the proper dyadic subgroup ``mu_16`` in ``F_4001``.
It verifies three exact finite-field certificates:

* a quotient-constant stack has all ``choose(8,5)=56`` distinct boundary
  interpolation scalars;
* the same quotient pencil has *zero* proper projective incidences with the
  radius-five syndrome ball, so the boundary witness dies completely one
  Hamming step earlier in this toy lift;
* two independently found Schubert pencils have respectively 12 and 13
  proper predecessor incidences.  They show the predecessor is nontrivial,
  but neither violates the candidate length cap 16.

The calculation enumerates every support of size at most five.  It is a
falsifier/certificate, not a proof of the production cap.
"""

from itertools import combinations


P = 4001
N = 16
K = 8
D = N - K
E = 5


def inv(x: int) -> int:
    return pow(x % P, P - 2, P)


def primitive_root() -> int:
    factors = []
    value = P - 1
    prime = 2
    while prime * prime <= value:
        if value % prime == 0:
            factors.append(prime)
            while value % prime == 0:
                value //= prime
        prime += 1
    if value > 1:
        factors.append(value)
    return next(
        g
        for g in range(2, P)
        if all(pow(g, (P - 1) // prime, P) != 1 for prime in factors)
    )


GEN = pow(primitive_root(), (P - 1) // N, P)
DOMAIN = [pow(GEN, i, P) for i in range(N)]
assert len(set(DOMAIN)) == N


def nullspace(rows: list[list[int]], ncols: int) -> list[list[int]]:
    matrix = [[entry % P for entry in row] for row in rows]
    pivots: list[int] = []
    row = 0
    for col in range(ncols):
        pivot = next(
            (candidate for candidate in range(row, len(matrix)) if matrix[candidate][col]),
            None,
        )
        if pivot is None:
            continue
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        scale = inv(matrix[row][col])
        matrix[row] = [scale * entry % P for entry in matrix[row]]
        for other in range(len(matrix)):
            if other != row and matrix[other][col]:
                scale = matrix[other][col]
                matrix[other] = [
                    (entry - scale * pivot_entry) % P
                    for entry, pivot_entry in zip(matrix[other], matrix[row])
                ]
        pivots.append(col)
        row += 1
        if row == len(matrix):
            break
    free = [col for col in range(ncols) if col not in pivots]
    basis = []
    for free_col in free:
        vector = [0] * ncols
        vector[free_col] = 1
        for pivot_row, pivot_col in enumerate(pivots):
            vector[pivot_col] = -matrix[pivot_row][free_col] % P
        basis.append(vector)
    return basis


# Column rescaling does not change a support span, so the ordinary Vandermonde
# parity frame suffices for the projective incidence enumeration.
COLUMNS = [[pow(x, degree, P) for degree in range(D)] for x in DOMAIN]
SUPPORT_NORMALS: list[tuple[tuple[int, ...], list[list[int]]]] = []
for size in range(1, E + 1):
    for support in combinations(range(N), size):
        normals = nullspace(
            [[COLUMNS[index][degree] for degree in range(D)] for index in support], D
        )
        assert len(normals) == D - size
        SUPPORT_NORMALS.append((support, normals))


def dot(left: list[int], right: list[int]) -> int:
    return sum(x * y for x, y in zip(left, right)) % P


def projective_incidence_labels(a: list[int], b: list[int]) -> set[int]:
    """Proper line intersections; ``P`` is the infinity-slot sentinel."""

    labels: set[int] = set()
    for _support, normals in SUPPORT_NORMALS:
        image_a = [dot(normal, a) for normal in normals]
        image_b = [dot(normal, b) for normal in normals]
        if not any(image_a) and not any(image_b):
            # The whole pencil lies in this support span: not MCA-proper.
            continue
        dependent = all(
            (image_a[i] * image_b[j] - image_a[j] * image_b[i]) % P == 0
            for i in range(len(normals))
            for j in range(i + 1, len(normals))
        )
        if not dependent:
            continue
        nonzero_b = next((i for i, value in enumerate(image_b) if value), None)
        if nonzero_b is None:
            labels.add(P)
            continue
        gamma = -image_a[nonzero_b] * inv(image_b[nonzero_b]) % P
        assert all(
            (left + gamma * right) % P == 0
            for left, right in zip(image_a, image_b)
        )
        labels.add(gamma)
    return labels


# On mu_n, the dual GRS multiplier is x/n.  These syndromes therefore belong
# to the same unscaled support-span frame used above.
def syndrome(word: list[int]) -> list[int]:
    n_inv = inv(N)
    return [
        sum(
            word[i] * DOMAIN[i] * n_inv * pow(DOMAIN[i], degree, P)
            for i in range(N)
        )
        % P
        for degree in range(D)
    ]


QUOTIENT_DOMAIN = []
for x in DOMAIN:
    y = x * x % P
    if y not in QUOTIENT_DOMAIN:
        QUOTIENT_DOMAIN.append(y)
assert len(QUOTIENT_DOMAIN) == 8


def leading_interpolation_scalar(support: tuple[int, ...], values: list[int]) -> int:
    leading = 0
    for i in support:
        denominator = 1
        for j in support:
            if i != j:
                denominator = denominator * (QUOTIENT_DOMAIN[i] - QUOTIENT_DOMAIN[j]) % P
        leading = (leading + values[i] * inv(denominator)) % P
    return -leading % P


# A fixed hyperplane-avoidance row certificate.
QUOTIENT_ROW = [875, 3390, 574, 311, 3970, 2599, 1417, 1587]
BOUNDARY_LABELS = {
    leading_interpolation_scalar(support, QUOTIENT_ROW)
    for support in combinations(range(8), 5)
}
assert len(BOUNDARY_LABELS) == 56

U0 = [QUOTIENT_ROW[QUOTIENT_DOMAIN.index(x * x % P)] for x in DOMAIN]
U1 = [pow(x, K, P) for x in DOMAIN]
QUOTIENT_PREDECESSOR = projective_incidence_labels(syndrome(U0), syndrome(U1))
assert QUOTIENT_PREDECESSOR == set()


# Exact rich-pencil certificates found by seeded four- and five-incidence
# Schubert searches.  The vectors are syndrome-space pencil generators.
FOUR_ANCHOR_A = [2953, 774, 2498, 1008, 3930, 139, 463, 3578]
FOUR_ANCHOR_B = [179, 853, 3158, 2578, 2873, 2931, 1520, 3260]
FIVE_ANCHOR_A = [2510, 1670, 1484, 1161, 2380, 2709, 1305, 2538]
FIVE_ANCHOR_B = [2900, 3881, 2685, 3691, 3693, 769, 1262, 1]

FOUR_ANCHOR_LABELS = projective_incidence_labels(FOUR_ANCHOR_A, FOUR_ANCHOR_B)
FIVE_ANCHOR_LABELS = projective_incidence_labels(FIVE_ANCHOR_A, FIVE_ANCHOR_B)
assert len(FOUR_ANCHOR_LABELS) == 12
assert len(FIVE_ANCHOR_LABELS) == 13


print(
    {
        "field": P,
        "domain_order": N,
        "boundary_distinct_scalars": len(BOUNDARY_LABELS),
        "quotient_predecessor_proper_incidence": len(QUOTIENT_PREDECESSOR),
        "four_anchor_predecessor_incidence": len(FOUR_ANCHOR_LABELS),
        "five_anchor_predecessor_incidence": len(FIVE_ANCHOR_LABELS),
        "candidate_length_cap": N,
    }
)
print("rate-half quotient-predecessor certificates reproduced")
