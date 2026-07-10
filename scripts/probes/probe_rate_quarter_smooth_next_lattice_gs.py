#!/usr/bin/env python3
"""Exact GS decode of the smooth F97 [32,8] counterexample one step lower.

The isolated-fibre construction has 36 nonjoint bad scalars at agreement 17.
This probe applies a multiplicity-one Guruswami--Sudan interpolation polynomial
of (1,7)-weighted degree 17.  There are 33 allowed monomials and 32 evaluation
constraints, so every degree-<8 polynomial with at least 18 agreements is a
linear Y-factor of the interpolation polynomial.  Factoring over F_97 therefore
gives an exact complete list for every one of the 97 affine-line scalars.

For each candidate factor q, the script computes its full agreement set and
checks the MCA no-joint clause by unique interpolation of both received rows.
This is an exact census of the next lattice point (agreement 18) for this one
stack, not a uniform theorem over all stacks.
"""

from __future__ import annotations

import sympy as sp


P = 97
N = 32
K = 8
OMEGA = 28
U0 = [
    0, 0, 77, 0, 0, 0, 0, 0, 0, 59, 53, 54, 54, 26, 84, 45,
    0, 0, 20, 0, 0, 0, 0, 0, 0, 38, 44, 43, 43, 71, 13, 52,
]
U1 = [
    0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2,
    0, 0, 46, 0, 0, 0, 0, 0, 0, 16, 24, 38, 36, 93, 7, 2,
]
XS = [pow(OMEGA, i, P) for i in range(N)]


def inv(x: int) -> int:
    assert x % P
    return pow(x % P, P - 2, P)


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] % P == 0:
        a.pop()
    return [x % P for x in a]


def add(a: list[int], b: list[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out)


def scale(c: int, a: list[int]) -> list[int]:
    return trim([(c * x) % P for x in a])


def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def eval_poly(a: list[int], x: int) -> int:
    out = 0
    for c in reversed(a):
        out = (out * x + c) % P
    return out


def interpolate(points: list[tuple[int, int]]) -> list[int]:
    out = [0]
    for i, (x, y) in enumerate(points):
        basis = [1]
        denominator = 1
        for j, (z, _) in enumerate(points):
            if i == j:
                continue
            basis = mul(basis, [(-z) % P, 1])
            denominator = denominator * (x - z) % P
        out = add(out, scale(y * inv(denominator), basis))
    return trim(out)


def null_vector(matrix: list[list[int]]) -> list[int]:
    a = [[x % P for x in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    pivots: list[int] = []
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = inv(a[r][c])
        a[r] = [z * x % P for x in a[r]]
        for i in range(rows):
            if i == r or not a[i][c]:
                continue
            z = a[i][c]
            a[i] = [(x - z * y) % P for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = next(c for c in range(cols) if c not in pivots)
    v = [0] * cols
    v[free] = 1
    for i, c in enumerate(pivots):
        v[c] = -a[i][free] % P
    assert all(sum(x * y for x, y in zip(row, v)) % P == 0 for row in matrix)
    return v


X, Y = sp.symbols("X Y")


def gs_candidates(word: list[int]) -> list[list[int]]:
    weighted_degree = 17
    monomials = [
        (i, j)
        for j in range(weighted_degree // (K - 1) + 1)
        for i in range(weighted_degree - (K - 1) * j + 1)
    ]
    assert len(monomials) == 33
    matrix = [
        [pow(x, i, P) * pow(y, j, P) % P for i, j in monomials]
        for x, y in zip(XS, word)
    ]
    coeffs = null_vector(matrix)
    qparts = []
    for j in range(3):
        expr = sum(c * X**i for c, (i, jj) in zip(coeffs, monomials) if jj == j)
        qparts.append(sp.Poly(expr, X, modulus=P))
    q0, q1, q2 = qparts
    candidates = []

    def add_rational_root(numerator: sp.Poly, denominator: sp.Poly) -> None:
        q, rem = sp.div(numerator, denominator, domain=sp.GF(P))
        if not rem.is_zero or q.degree() >= K:
            return
        # Verify the quadratic identity exactly over GF(P).
        identity = q2 * q * q + q1 * q + q0
        if not identity.is_zero:
            return
        coeff_high = [int(c) % P for c in q.all_coeffs()]
        candidates.append(trim(list(reversed(coeff_high))))

    if q2.is_zero:
        assert not q1.is_zero
        add_rational_root(-q0, q1)
    else:
        discriminant = q1 * q1 - sp.Poly(4, X, modulus=P) * q2 * q0
        if discriminant.is_zero:
            square_roots = [sp.Poly(0, X, modulus=P)]
        else:
            content, factors = sp.factor_list(discriminant, modulus=P)
            content_mod = int(content) % P
            scalar_roots = [z for z in range(P) if z * z % P == content_mod]
            if any(multiplicity % 2 for _, multiplicity in factors):
                square_roots = []
            else:
                root_expr = 1
                for factor, multiplicity in factors:
                    root_expr *= factor.as_expr() ** (multiplicity // 2)
                square_roots = [sp.Poly(z * root_expr, X, modulus=P)
                                for z in scalar_roots]
        denominator = sp.Poly(2, X, modulus=P) * q2
        for square_root in square_roots:
            add_rational_root(-q1 + square_root, denominator)
    # Every returned polynomial must satisfy the interpolation identity.
    unique = []
    seen = set()
    for q in candidates:
        key = tuple(q)
        if key in seen:
            continue
        seen.add(key)
        unique.append(q)
    return unique


def row_is_degree_lt_k(row: list[int], support: list[int]) -> bool:
    if len(support) <= K:
        return True
    q = interpolate([(XS[i], row[i]) for i in support[:K]])
    assert len(q) - 1 < K
    return all(eval_poly(q, XS[i]) == row[i] for i in support)


def main() -> None:
    assert pow(OMEGA, N, P) == 1 and pow(OMEGA, N // 2, P) != 1
    histogram: dict[int, int] = {}
    bad18 = []
    all_lists = {}
    for gamma in range(P):
        word = [(a + gamma * b) % P for a, b in zip(U0, U1)]
        candidates = gs_candidates(word)
        decoded = []
        is_bad = False
        for q in candidates:
            support = [i for i, (x, y) in enumerate(zip(XS, word))
                       if eval_poly(q, x) == y]
            if len(support) < 18:
                continue
            joint = (
                row_is_degree_lt_k(U0, support)
                and row_is_degree_lt_k(U1, support)
            )
            decoded.append((q, support, joint))
            if not joint:
                is_bad = True
        histogram[len(decoded)] = histogram.get(len(decoded), 0) + 1
        if decoded:
            all_lists[gamma] = decoded
        if is_bad:
            bad18.append(gamma)

    # The factorization argument is complete: every >=18-agreement polynomial
    # divides the chosen Q as Y-q(X), so no list element is omitted.
    print({
        "p": P,
        "n": N,
        "k": K,
        "agreement_threshold": 18,
        "list_size_histogram": histogram,
        "scalars_with_nonempty_list": len(all_lists),
        "mca_bad_scalars": bad18,
        "mca_bad_count": len(bad18),
        "n_bound_holds_for_this_stack": len(bad18) <= N,
        "maximum_list_size": max(histogram),
        "decoded_details": {
            gamma: [(q, support, joint) for q, support, joint in values]
            for gamma, values in all_lists.items()
        },
    })


if __name__ == "__main__":
    main()
