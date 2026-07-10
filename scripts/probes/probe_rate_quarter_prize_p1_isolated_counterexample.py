#!/usr/bin/env python3
"""Exact arithmetic certificate for the rate-quarter construction at prize P1.

This lifts `probe_rate_quarter_smooth_isolated_counterexample.py` from mu_32
to the actual mu_(2^30) evaluation domain.  Put m=2^26, n=16m and k=4m.
The map x |-> x^m has the 16 fibres of mu_n, each of size m.  The universal
mu_16 cubic-locator identity supplies three collapsed polynomial lines with
pair cores of three fibres, two private fibres per 2k-core, and one uncovered
fibre.  Primitive direction (X,1) keeps both line components below degree k.

The 15 covered fibres yield 15m distinct safe bad scalars gamma=-x.  On the
uncovered fibre, a generic affine pair (alpha*x,beta) yields three multiplicative
cosets of m additional bad scalars.  The script searches alpha,beta and verifies
exactly the group-theoretic conditions making those cosets nonzero, pairwise
disjoint, and disjoint from the entire smooth domain.

The result is an exact integer/modular certificate for 18m=(9/8)n explicit
nonjoint half-predecessor witnesses.  It also checks the maximal *thickening*:
partition all but one point of the old hole among the three private cores.
For r=(m-1)/3 this raises every core from 8m to 8m+r, leaves one isolated
point, and still gives n+2 bad scalars at agreement 8m+r+1.  It avoids
enumerating the billion-point domain; a Lean transcription must prove the
fibre cardinalities and the pointwise witness formulas abstractly.
"""

from __future__ import annotations


P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
M = 2**26
K = 2**28


def inv(x: int) -> int:
    assert x % P
    return pow(x % P, P - 2, P)


def add(a: list[int], b: list[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] = (out[i] + x) % P
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale(c: int, a: list[int]) -> list[int]:
    return [(c * x) % P for x in a]


def mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return out


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
    assert pow(G, N, P) == 1 and pow(G, N // 2, P) != 1
    zeta = pow(G, M, P)
    assert pow(zeta, 16, P) == 1 and pow(zeta, 8, P) == P - 1

    a_exp = {0, 1, 8}
    b_exp = {2, 9, 10}
    c_exp = {3, 5, 7}
    p_a = locator([pow(zeta, e, P) for e in sorted(a_exp)])
    p_b = locator([pow(zeta, e, P) for e in sorted(b_exp)])
    p_c = locator([pow(zeta, e, P) for e in sorted(c_exp)])

    two_inv = inv(2)
    lam_formula = (
        1 - pow(zeta, 2, P) - pow(zeta, 4, P) - pow(zeta, 6, P)
    ) * two_inv % P
    lam = next(
        (p_c[j] - p_a[j]) * inv(p_b[j] - p_a[j]) % P
        for j in range(3) if p_a[j] != p_b[j]
    )
    assert lam == lam_formula
    assert p_c == add(scale(1 - lam, p_a), scale(lam, p_b))

    # f1=0, f2=(1-lambda)p_A(X^m), f3=p_C(X^m).
    # Their degrees are 0 and 3m; multiplying by X for the intercept gives
    # degree 3m+1 < 4m=k.
    assert 3 * M + 1 < K

    used = a_exp | b_exp | c_exp
    unique = [{4, 6}, {11, 12}, {13, 14}]
    hole_exp = 15
    assert set().union(*unique, {hole_exp}) == set(range(16)) - used

    y_hole = pow(zeta, hole_exp, P)
    t = [
        0,
        (1 - lam) * eval_poly(p_a, y_hole) % P,
        eval_poly(p_c, y_hole),
    ]
    assert len(set(t)) == 3 and all(x != 0 for x in t[1:])

    alpha = beta = None
    constants: list[int] = []
    for aa in range(1, 200):
        for bb in range(1, 200):
            if any(bb == ti for ti in t):
                continue
            cs = [(ti - aa) * inv(bb - ti) % P for ti in t]
            if any(c == 0 or pow(c, N, P) == 1 for c in cs):
                continue
            if any(pow(cs[i] * inv(cs[j]) % P, M, P) == 1
                   for i in range(3) for j in range(i)):
                continue
            alpha, beta, constants = aa, bb, cs
            break
        if alpha is not None:
            break
    assert alpha is not None and beta is not None

    # Exact cardinal ledger.  Pair roots: 3m.  Private part of each core: 2m.
    # Each core: 2*(3m)+2m=8m=2k.  Their union: 15m.  Hole: m.
    pair_core = 3 * M
    private_core = 2 * M
    core = 2 * pair_core + private_core
    covered = 15 * M
    hole = M
    safe_bad = covered
    unsafe_bad = 3 * hole
    total_bad = safe_bad + unsafe_bad
    assert core == 2 * K
    assert covered + hole == N
    assert total_bad == 18 * M
    assert total_bad * 8 == 9 * N
    assert total_bad > N

    # Maximal thickening.  Since m=2^26=1 (mod 3), partition m-1 old-hole
    # coordinates into three disjoint r-sets and assign one to each line core.
    # A moved point owned by line j is still a safe fresh point for every
    # source i!=j: at gamma=-x both folded values are zero.  The distinct t_i
    # certify the required cross-line mismatch.  The one residual point keeps
    # the three old unsafe labels, whose separation was checked above.
    thickening = (M - 1) // 3
    assert M == 3 * thickening + 1
    thick_core = core + thickening
    thick_covered = covered + 3 * thickening
    thick_hole = M - 3 * thickening
    thick_safe_bad = thick_covered
    thick_unsafe_bad = 3 * thick_hole
    thick_total_bad = thick_safe_bad + thick_unsafe_bad
    thick_threshold = thick_core + 1
    thick_radius_numerator = N - thick_threshold
    assert thick_hole == 1
    assert thick_total_bad == N + 2
    assert thick_threshold == (25 * M + 2) // 3
    assert thick_radius_numerator == (23 * M - 2) // 3
    assert 48 * M * thick_radius_numerator == (23 * M - 2) * N
    assert all(ti != tj for i, ti in enumerate(t) for tj in t[:i])

    # Representative pointwise equations on the hole fibre.  If x^m=y_hole,
    # then f_i(x)=t_i and gamma=c_i*x makes
    #   alpha*x + gamma*beta = t_i*(x+gamma).
    x0 = pow(G, hole_exp, P)
    assert pow(x0, M, P) == y_hole
    for ti, ci in zip(t, constants):
        gamma = ci * x0 % P
        assert (alpha * x0 + gamma * beta) % P == ti * (x0 + gamma) % P

    print({
        "P": P,
        "n": N,
        "k": K,
        "m": M,
        "zeta16": zeta,
        "lambda": lam,
        "locator_A": p_a,
        "locator_B": p_b,
        "locator_C": p_c,
        "hole_factor_values": t,
        "alpha": alpha,
        "beta": beta,
        "unsafe_coset_constants": constants,
        "unsafe_constants_outside_mu_n": [pow(c, N, P) for c in constants],
        "pairwise_ratio_mth_powers": [
            pow(constants[i] * inv(constants[j]) % P, M, P)
            for i in range(3) for j in range(i)
        ],
        "agreement_threshold": 2 * K + 1,
        "safe_bad_scalars": safe_bad,
        "unsafe_bad_scalars": unsafe_bad,
        "total_bad_scalars": total_bad,
        "relative_to_n": "9/8",
        "n_scalar_bound_refuted": total_bad > N,
        "maximal_thickening_per_core": thickening,
        "thickened_core_size": thick_core,
        "thickened_residual_hole": thick_hole,
        "thickened_agreement_threshold": thick_threshold,
        "thickened_radius_numerator": thick_radius_numerator,
        "thickened_safe_bad_scalars": thick_safe_bad,
        "thickened_unsafe_bad_scalars": thick_unsafe_bad,
        "thickened_total_bad_scalars": thick_total_bad,
        "thickened_excess_over_n": thick_total_bad - N,
    })


if __name__ == "__main__":
    main()
