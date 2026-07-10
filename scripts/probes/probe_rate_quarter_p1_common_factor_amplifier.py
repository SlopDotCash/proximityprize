#!/usr/bin/env python3
"""Exact P1 certificate for the rate-quarter common-factor amplifier.

Starting from the maximally thickened three-line mu_16 cell, choose `d`
singleton coordinates of owner 0 and `d` of owner 1 as roots of a common
factor G.  They become triple-core (dead) coordinates.  Turn `d` singleton
coordinates of owner 2 into isolated holes.  The two-for-one trade keeps the
one-fresh scalar count at n+2 and raises every core by d.

At the degree limit d=(m-2)/2 this checks the exact agreement/radius
arithmetic and searches explicit isolated-hole rows on the new fibre.  It
also checks all unsafe multiplicative cosets against one another and against
the smooth domain.  No billion-point enumeration is performed.
"""

from __future__ import annotations


P = 365375409332725729550921208179070755120141565953
GEN = 303645430271030343624574566109998498685964493478
N = 2**30
M = 2**26
K = 2**28
R = (M - 1) // 3
D = (M - 2) // 2


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


def find_row(values: list[int], forbidden_ids: set[int]) -> tuple[int, int, list[int], list[int]]:
    """Find (alpha,beta) whose three label cosets are new and outside mu_n."""
    for alpha in range(1, 500):
        for beta in range(1, 500):
            if any(beta == t for t in values):
                continue
            constants = [(t - alpha) * inv(beta - t) % P for t in values]
            if any(c == 0 or pow(c, N, P) == 1 for c in constants):
                continue
            ids = [pow(c, M, P) for c in constants]
            if len(set(ids)) != 3 or any(x in forbidden_ids for x in ids):
                continue
            return alpha, beta, constants, ids
    raise AssertionError("no isolated row found in search box")


def main() -> None:
    assert pow(GEN, N, P) == 1 and pow(GEN, N // 2, P) != 1
    zeta = pow(GEN, M, P)
    assert pow(zeta, 16, P) == 1 and pow(zeta, 8, P) == P - 1

    p_a = locator([pow(zeta, e, P) for e in (0, 1, 8)])
    p_b = locator([pow(zeta, e, P) for e in (2, 9, 10)])
    p_c = locator([pow(zeta, e, P) for e in (3, 5, 7)])
    lam = (1 - pow(zeta, 2, P) - pow(zeta, 4, P) - pow(zeta, 6, P)) * inv(2) % P
    assert p_c == add(scale(1 - lam, p_a), scale(lam, p_b))

    # Base factor values on the old isolated fibre 15 and the new-hole
    # singleton fibre 13.  Both triples must be distinct.
    def factor_values(exp: int) -> list[int]:
        y = pow(zeta, exp, P)
        return [
            0,
            (1 - lam) * eval_poly(p_a, y) % P,
            eval_poly(p_c, y),
        ]

    values15 = factor_values(15)
    values13 = factor_values(13)
    assert len(set(values15)) == 3
    assert len(set(values13)) == 3

    # A label gamma=c*x with x^m=zeta^a occupies the multiplicative coset
    # identified by gamma^m=c^m*zeta^a.  Search the two rows sequentially so
    # all six identifiers are distinct.  c^n != 1 keeps every label outside
    # the full smooth domain (and hence outside every safe label -x).
    alpha15, beta15, constants15, raw_ids15 = find_row(values15, set())
    ids15 = [x * pow(zeta, 15, P) % P for x in raw_ids15]
    assert len(set(ids15)) == 3

    # `find_row` works with raw c^m identifiers, so translate the forbidden
    # fibre-15 identifiers to the raw scale appropriate for fibre 13.
    forbidden_raw13 = {
        x * inv(pow(zeta, 13, P)) % P
        for x in ids15
    }
    alpha13, beta13, constants13, raw_ids13 = find_row(values13, forbidden_raw13)
    ids13 = [x * pow(zeta, 13, P) % P for x in raw_ids13]
    assert len(set(ids15 + ids13)) == 6

    # Degree and ownership ledger at maximal amplification.
    assert M == 3 * R + 1
    assert 2 * D == M - 2
    base_core = 8 * M + R
    amplified_core = base_core + D
    threshold = amplified_core + 1
    radius_numerator = N - threshold
    triple = 2 * D
    holes = D + 1
    proper = N - triple - holes
    bad = proper + 3 * holes

    assert 3 * M + 2 * D + 1 == K - 1  # degree of X*G*f_i
    assert amplified_core == (53 * M - 8) // 6
    assert threshold == (53 * M - 2) // 6
    assert radius_numerator == (43 * M + 2) // 6
    assert 96 * radius_numerator == 43 * N + 32
    assert bad == N + 2
    assert 2 * holes - triple == 2

    # Pointwise scaled-hole identity.  For x in fibre a and H=G(x)!=0,
    # alpha*x*H + (c*x)*(beta*H) = (H*t_i)*(x+c*x).
    # The nonzero H cancels, so it suffices to check the base identity.
    for exp, values, alpha, beta, constants in (
        (15, values15, alpha15, beta15, constants15),
        (13, values13, alpha13, beta13, constants13),
    ):
        x = pow(GEN, exp, P)
        assert pow(x, M, P) == pow(zeta, exp, P)
        for t, c in zip(values, constants):
            assert (alpha * x + c * x * beta) % P == t * (x + c * x) % P

    print({
        "P": P,
        "n": N,
        "m": M,
        "k": K,
        "r": R,
        "amplifier_steps": D,
        "common_factor_degree": 2 * D,
        "triple_core": triple,
        "holes": holes,
        "amplified_core": amplified_core,
        "agreement_threshold": threshold,
        "radius_numerator": radius_numerator,
        "radius": f"{radius_numerator}/{N}",
        "closed_form": "43/96 + 1/(3n)",
        "bad_scalars": bad,
        "excess_over_n": bad - N,
        "old_hole_row": [alpha15, beta15],
        "new_hole_row": [alpha13, beta13],
        "old_hole_factor_values": values15,
        "new_hole_factor_values": values13,
        "old_hole_constants": constants15,
        "new_hole_constants": constants13,
        "unsafe_coset_ids": ids15 + ids13,
    })


if __name__ == "__main__":
    main()
