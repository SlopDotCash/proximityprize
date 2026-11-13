#!/usr/bin/env python3
"""Exact base-field certificate for the three-core rate-half counterexample.

The 64-point calculation is performed directly modulo the first certified
prize prime.  Its 93 projective defect directions tensor with the m-point
radix Vandermonde family, producing 93*m directions at length 64*m.
"""

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
M = 2**24
BASE_LENGTH = 64
BASE_DIMENSION = 32

CORE_MASKS = [
    542424784538028885,
    16114235817432360298,
    3975377171011979844,
]


def _require(condition, detail):
    """Keep the certificate checks active under Python optimization."""
    if not condition:
        raise AssertionError(detail)


def inverse(value: int) -> int:
    return pow(value, P - 2, P)


base_generator = pow(G, M, P)
_require(pow(base_generator, BASE_LENGTH, P) == 1,
         "base generator order does not divide 64")
_require(pow(base_generator, BASE_LENGTH // 2, P) == P - 1,
         "base generator is not a primitive 64th root of unity")
domain = [pow(base_generator, i, P) for i in range(BASE_LENGTH)]
cores = [
    {i for i in range(BASE_LENGTH) if (mask >> i) & 1}
    for mask in CORE_MASKS
]
_require(all(len(core) == 33 for core in cores), "a core does not have 33 points")


def core_constraint(core: set[int]) -> list[int]:
    """The unique parity check of RS_32 restricted to a 33-set."""
    result = [0] * BASE_LENGTH
    for i in core:
        denominator = 1
        for j in core:
            if i != j:
                denominator = denominator * (domain[i] - domain[j]) % P
        result[i] = inverse(denominator)
    return result


def external_defect(core: set[int], outside: int) -> list[int]:
    """Evaluation error at outside after interpolation on 32 core points."""
    basis = sorted(core)[:BASE_DIMENSION]
    result = [0] * BASE_LENGTH
    result[outside] = 1
    for j in basis:
        numerator = 1
        denominator = 1
        for h in basis:
            if h != j:
                numerator = numerator * (domain[outside] - domain[h]) % P
                denominator = denominator * (domain[j] - domain[h]) % P
        result[j] = -numerator * inverse(denominator) % P
    return result


def rref(rows: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    rows = [row[:] for row in rows]
    pivots: list[int] = []
    for rank in range(len(rows)):
        pivot = next(
            column
            for column in range(BASE_LENGTH)
            if any(rows[j][column] for j in range(rank, len(rows)))
        )
        source = next(j for j in range(rank, len(rows)) if rows[j][pivot])
        rows[rank], rows[source] = rows[source], rows[rank]
        scale = inverse(rows[rank][pivot])
        rows[rank] = [entry * scale % P for entry in rows[rank]]
        for j in range(len(rows)):
            if j != rank and rows[j][pivot]:
                scale = rows[j][pivot]
                rows[j] = [
                    (entry - scale * pivot_entry) % P
                    for entry, pivot_entry in zip(rows[j], rows[rank])
                ]
        pivots.append(pivot)
    return rows, pivots


def reduce_mod_constraints(
    vector: list[int], rows: list[list[int]], pivots: list[int]
) -> list[int]:
    vector = vector[:]
    for row, pivot in zip(rows, pivots):
        scale = vector[pivot]
        if scale:
            vector = [
                (entry - scale * pivot_entry) % P
                for entry, pivot_entry in zip(vector, row)
            ]
    return vector


def projective_normalize(vector: list[int]) -> tuple[int, ...]:
    first = next(entry for entry in vector if entry)
    scale = inverse(first)
    return tuple(entry * scale % P for entry in vector)


constraint_rows, pivots = rref([core_constraint(core) for core in cores])
directions = [
    projective_normalize(
        reduce_mod_constraints(
            external_defect(core, outside), constraint_rows, pivots
        )
    )
    for core in cores
    for outside in sorted(set(range(BASE_LENGTH)) - core)
]

# A single two-coordinate projective chart already separates all 93 classes.
# This is useful for a compact formal certificate: no 93-by-93 comparison is
# needed once coordinate 6 is known nonzero.
raw_directions = [
    reduce_mod_constraints(
        external_defect(core, outside), constraint_rows, pivots
    )
    for core in cores
    for outside in sorted(set(range(BASE_LENGTH)) - core)
]
fingerprint = [
    vector[15] * inverse(vector[6]) % P for vector in raw_directions
]

_require(len(constraint_rows) == 3, "constraint rank is not 3")
_require(len(directions) == 93, "there are not 93 defect directions")
_require(len(set(directions)) == 93, "the 93 projective directions are not distinct")
_require(all(vector[6] != 0 for vector in raw_directions),
         "coordinate 6 is zero on a defect direction")
_require(len(set(fingerprint)) == 93, "the (6, 15) chart does not separate all 93 classes")

length = BASE_LENGTH * M
lifted_directions = len(directions) * M
_require(length == 2**30, "lifted length is not 2^30")
_require(lifted_directions == 1_560_281_088, "lifted direction count is not 93 * 2^24")
_require(lifted_directions - length == 29 * M == 486_539_264,
         "excess over length is not 29 * 2^24")

# A union of fewer than q proper hyperplanes cannot cover a finite vector
# space over F_q.  First avoid the 93m denominator kernels; after fixing that
# vector, avoid one collision hyperplane for every pair of directions.
_require(len(directions) * M < P, "denominator kernels do not fit below q")
_require(lifted_directions * (lifted_directions - 1) // 2 < P,
         "collision hyperplanes do not fit below q")

print(
    "base=64 cores=3 core_size=33 constraint_rank=3 "
    "base_projective_directions=93 fingerprint_coordinates=6,15"
)
print(
    f"m={M} length={length} lifted_directions={lifted_directions} "
    f"excess_over_length={lifted_directions - length}"
)
print("hyperplane_avoidance_budget=PASS")
