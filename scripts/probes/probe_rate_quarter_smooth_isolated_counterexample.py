#!/usr/bin/env python3
"""Exact smooth-domain rate-quarter counterexample over F_97.

This is the subgroup lift of the arbitrary-domain primitive-isolated
construction.  Put n=32, k=8, m=2 and let y=x^m map mu_32 onto mu_16.
Three universal collinear cubic locators on mu_16 have disjoint root triples

    A={0,1,8}, B={2,9,10}, C={3,5,7}.

Lifting their roots gives three disjoint six-coordinate pair cores.  Adding
two unused mu_m-fibres to each line makes three 16-coordinate cores, leaving
one two-coordinate fibre uncovered.  With primitive direction (X,1), the 30
covered coordinates yield 30 distinct bad scalars gamma=-x.  A generic affine
row on the uncovered fibre yields three disjoint two-scalar cosets, for a total
of 36>32 explicit nonjoint half-predecessor bad scalars.

Every displayed witness is checked directly.  This proves that smooth
2-power subgroup structure does not rescue the uniform n-scalar bound at
rate 1/4; it is an executable certificate, pending a Lean transcription.
"""

from __future__ import annotations

from itertools import product


P = 97
N = 32
K = 8
M = 2


def inv(x: int) -> int:
    assert x % P
    return pow(x % P, P - 2, P)


def primitive_root() -> int:
    for g in range(2, P):
        if pow(g, 48, P) != 1 and pow(g, 32, P) != 1:
            return g
    raise RuntimeError("no primitive root")


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


def sub(a: list[int], b: list[int]) -> list[int]:
    return add(a, [(-x) % P for x in b])


def scale(c: int, a: list[int]) -> list[int]:
    return trim([(c * x) % P for x in a])


def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


def compose_x_pow(a: list[int], m: int) -> list[int]:
    out = [0] * ((len(a) - 1) * m + 1)
    for i, c in enumerate(a):
        out[i * m] = c
    return trim(out)


def eval_poly(a: list[int], x: int) -> int:
    out = 0
    for c in reversed(a):
        out = (out * x + c) % P
    return out


def locator(values: list[int]) -> list[int]:
    out = [1]
    for x in values:
        out = mul(out, [(-x) % P, 1])
    return out


def main() -> None:
    omega = pow(primitive_root(), (P - 1) // N, P)
    xs = [pow(omega, e, P) for e in range(N)]
    zeta = pow(omega, M, P)
    assert pow(zeta, 16, P) == 1 and pow(zeta, 8, P) == P - 1

    a_exp = {0, 1, 8}
    b_exp = {2, 9, 10}
    c_exp = {3, 5, 7}
    p_a = locator([pow(zeta, e, P) for e in sorted(a_exp)])
    p_b = locator([pow(zeta, e, P) for e in sorted(b_exp)])
    p_c = locator([pow(zeta, e, P) for e in sorted(c_exp)])

    # p_C=(1-lambda)p_A+lambda*p_B; solve and verify all coefficients.
    lam = next(
        (p_c[j] - p_a[j]) * inv(p_b[j] - p_a[j]) % P
        for j in range(3) if p_a[j] != p_b[j]
    )
    assert p_c == add(scale(1 - lam, p_a), scale(lam, p_b))

    f1 = [0]
    f2 = compose_x_pow(scale(1 - lam, p_a), M)
    f3 = compose_x_pow(p_c, M)
    fs = [f1, f2, f3]
    assert sub(f2, f1) == f2
    assert sub(f3, f2) == compose_x_pow(scale(lam, p_b), M)
    assert all(len(f) - 1 < K for f in fs)

    used = a_exp | b_exp | c_exp
    remaining = set(range(16)) - used
    hole_exp = 15
    assert hole_exp in remaining
    unique_exp = [{4, 6}, {11, 12}, {13, 14}]
    assert set().union(*unique_exp, {hole_exp}) == remaining

    def fibre(exponents: set[int]) -> set[int]:
        return {e for e in range(N) if e % 16 in exponents}

    e12 = fibre(a_exp)
    e23 = fibre(b_exp)
    e13 = fibre(c_exp)
    cores = [
        e12 | e13 | fibre(unique_exp[0]),
        e12 | e23 | fibre(unique_exp[1]),
        e13 | e23 | fibre(unique_exp[2]),
    ]
    hole = fibre({hole_exp})
    assert all(len(core) == 2 * K for core in cores)
    assert cores[0] & cores[1] == e12
    assert cores[1] & cores[2] == e23
    assert cores[0] & cores[2] == e13
    assert len(set().union(*cores)) == N - M
    assert len(hole) == M and not (set().union(*cores) & hole)

    # Search a constant affine pair (alpha*x,beta) on the uncovered fibre.
    # Its three scalar maps are multiplication by distinct H-coset constants.
    alpha = beta = None
    for aa, bb in product(range(1, P), repeat=2):
        constants = []
        ok = True
        for f in fs:
            t = eval_poly(f, xs[next(iter(hole))])
            if bb == t:
                ok = False
                break
            constants.append((t - aa) * inv(bb - t) % P)
        if not ok:
            continue
        unsafe_sets = [{c * xs[e] % P for e in hole} for c in constants]
        safe = {(-xs[e]) % P for e in set().union(*cores)}
        if any(safe & s for s in unsafe_sets):
            continue
        if any(unsafe_sets[i] & unsafe_sets[j]
               for i in range(3) for j in range(i)):
            continue
        alpha, beta = aa, bb
        break
    assert alpha is not None and beta is not None

    u0 = [0] * N
    u1 = [0] * N
    for e, x in enumerate(xs):
        owners = [i for i, core in enumerate(cores) if e in core]
        if not owners:
            assert e in hole
            u0[e], u1[e] = alpha * x % P, beta
            continue
        values = {eval_poly(fs[i], x) for i in owners}
        assert len(values) == 1
        value = values.pop()
        u0[e], u1[e] = value * x % P, value

    witnesses: dict[int, list[tuple[int, int]]] = {}
    for i, (f, core) in enumerate(zip(fs, cores)):
        ai = mul(f, [0, 1])
        ri = f
        assert len(ai) - 1 < K and len(ri) - 1 < K
        for e, x in enumerate(xs):
            if e in core:
                continue
            denominator = (u1[e] - eval_poly(ri, x)) % P
            numerator = (eval_poly(ai, x) - u0[e]) % P
            assert denominator
            gamma = numerator * inv(denominator) % P
            q = add(ai, scale(gamma, ri))
            assert len(q) - 1 < K
            support = set(core) | {e}
            assert len(support) == 2 * K + 1
            for j in support:
                assert eval_poly(q, xs[j]) == (u0[j] + gamma * u1[j]) % P
            # The 2k-point core uniquely fixes (a_i,r_i); at the fresh point
            # at least one row differs, so no joint degree-<k pair exists.
            assert (eval_poly(ai, x), eval_poly(ri, x)) != (u0[e], u1[e])
            witnesses.setdefault(gamma, []).append((i, e))

    safe_scalars = {(-xs[e]) % P for e in set().union(*cores)}
    unsafe_scalars = set(witnesses) - safe_scalars
    assert len(safe_scalars) == N - M
    assert len(unsafe_scalars) == 3 * M
    assert len(witnesses) == 36 > N

    print({
        "p": P,
        "n": N,
        "k": K,
        "agreement_threshold": 2 * K + 1,
        "omega": omega,
        "lambda": lam,
        "alpha": alpha,
        "beta": beta,
        "f1": f1,
        "f2": f2,
        "f3": f3,
        "core_exponents": [sorted(core) for core in cores],
        "hole_exponents": sorted(hole),
        "u0": u0,
        "u1": u1,
        "safe_bad_scalars": sorted(safe_scalars),
        "unsafe_bad_scalars": sorted(unsafe_scalars),
        "bad_scalar_lower_bound": len(witnesses),
        "n_scalar_bound_refuted": len(witnesses) > N,
    })


if __name__ == "__main__":
    main()
