#!/usr/bin/env python3
"""Exact F_59 certificate refuting a general n-bound for short cocircuits.

The represented matroid is the cycle matroid of K_8: use the oriented
incidence matrix with the eighth vertex row deleted. The singleton and
two-vertex shores give 36 bonds of weights 7 and 12 on 28 edges. The script
also checks an explicit affine chart whose gamma coordinate separates all 36
normal directions.
"""

from itertools import combinations

P = 59
V = 8
R = V - 1
EDGES = list(combinations(range(V), 2))

# Columns of the reduced oriented incidence matrix of K_8.
COLS = []
for i, j in EDGES:
    col = [0] * R
    if i < R:
        col[i] = 1
    if j < R:
        col[j] = -1 % P
    COLS.append(tuple(col))

ELL0 = (19, 48, 49, 55, 22, 42, 5)
ELL1 = (35, 30, 32, 42, 17, 43, 52)


def dot(x, y):
    return sum(a * b for a, b in zip(x, y)) % P


def rank(rows):
    """Exact row rank modulo P."""
    a = [[x % P for x in row] for row in rows]
    if not a:
        return 0
    m, n = len(a), len(a[0])
    pivot = 0
    for col in range(n):
        hit = next((i for i in range(pivot, m) if a[i][col]), None)
        if hit is None:
            continue
        a[pivot], a[hit] = a[hit], a[pivot]
        inv = pow(a[pivot][col], -1, P)
        a[pivot] = [(inv * x) % P for x in a[pivot]]
        for i in range(m):
            if i != pivot and a[i][col]:
                q = a[i][col]
                a[i] = [(x - q * y) % P for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == m:
            break
    return pivot


def cut_normal(vertices):
    """Potential 1_S modulo constants, in the chart potential(8)=0."""
    vertices = set(vertices)
    base = int(V - 1 in vertices)
    return tuple((int(i in vertices) - base) % P for i in range(R))


assert len(EDGES) == 28
assert rank([tuple(col[i] for col in COLS) for i in range(R)]) == R


def projective_normalize(v):
    first = next(x for x in v if x)
    inv = pow(first, -1, P)
    return tuple(inv * x % P for x in v)


# The graphic representation is loopless and simple.
assert all(any(col) for col in COLS)
assert len({projective_normalize(col) for col in COLS}) == len(COLS)

# ELL0 and ELL1 extend to an actual dual basis, so the ratio below is a
# literal affine normal coordinate after an invertible row transformation.
standard = [tuple(int(i == j) for i in range(R)) for j in range(5)]
assert rank([ELL0, ELL1] + standard) == R

gammas = {}
weights = set()
for size in (1, 2):
    for vertices in combinations(range(V), size):
        normal = cut_normal(vertices)
        word = tuple(dot(normal, col) for col in COLS)
        support = [e for e, value in enumerate(word) if value]
        zeros = [COLS[e] for e, value in enumerate(word) if not value]

        expected_weight = size * (V - size)
        assert len(support) == expected_weight
        assert 2 * expected_weight < len(EDGES)
        weights.add(expected_weight)

        # The zero columns span the kernel hyperplane of this normal. Hence
        # every row-space word supported inside this cut is its scalar multiple.
        assert rank(zeros) == R - 1

        denominator = dot(ELL0, normal)
        assert denominator != 0
        gamma = dot(ELL1, normal) * pow(denominator, -1, P) % P
        assert gamma not in gammas
        gammas[gamma] = tuple(v + 1 for v in vertices)

assert len(gammas) == 36 > len(EDGES)
assert 4 * (R - 2) <= len(EDGES)  # r <= n/4 + 2

print(
    "K8/F59 counterexample verified: "
    f"n={len(EDGES)}, rank={R}, short_cocircuits={len(gammas)}, "
    f"weights={sorted(weights)}, distinct_gammas={len(gammas)}"
)
