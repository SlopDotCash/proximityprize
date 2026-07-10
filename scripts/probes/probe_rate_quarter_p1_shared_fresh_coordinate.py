#!/usr/bin/env python3
r"""Shared-fresh-coordinate configuration at the P1 rate-quarter predecessor.

Context: [rate-quarter-joint-witness-bare-charge] (DISPROOF_LOG 2026-07-10)
proved that the bare MCA clauses do not make the scalar-to-fresh-coordinate
escape charge injective, and that any over-budget charge has THREE distinct
bad scalars whose witnesses share one fresh coordinate outside a known
threshold joint-agreement set.  This probe determines exactly what that
three-scalar shared-fresh-coordinate configuration forces for Reed--Solomon
codes, and whether it is realizable at all.

Part 1 (structural consequences motivating the probe):
  * divided-difference pencil: two witnesses (S1,p1,g1), (S2,p2,g2) with
    g1 != g2 produce codewords w1 = (p2-p1)/(g2-g1), w0 = p1 - g1*w1 with
    p_j = w0 + g_j*w1 and (w0,w1) = (u0,u1) on S1 /\ S2;
  * witness incomparability: S1 subset S2 is impossible for distinct bad
    scalars (the pencil would jointly explain on S1);
  * distinct line values at the shared coordinate when u1(i) != 0;
  * absorption dichotomy: if |S1 /\ S2 /\ J| >= k the pencil IS the known
    joint pair, so the shared coordinate i is absorbed into the maximal
    joint-agreement set of (q0,q1);
  * two-cover bound: |S1|+|S2|+|S3| <= n + 2|U| where U is the union of the
    pairwise intersections; if the three witness codewords are collinear
    (one common pencil), that pencil agrees with the stack on all of U.

  The explicit model below checks these consequences on that instance.  The
  deterministic pseudorandom loop separately regression-tests only the
  divided-difference pencil identity; it is not a proof of a universal law.

Part 2 (exact realizability countermodel):
  An explicit RS[8,2] instance over F_11 with a size-4 joint set
  J = {0,1,2,3}, three distinct bad scalars gamma in {1,2,3} at radius 1/2
  (threshold 4), witness sets {0,4,5,6}, {1,4,5,7}, {2,4,6,7} all containing
  the shared fresh coordinate 4 not in J, and with coordinate 4 NOT in the
  maximal joint set of (q0,q1).  Hence no code-agnostic (or even RS-generic)
  impossibility proof of the shared-fresh triple exists.  The matching Lean
  certificate is `_P1RateQuarterSharedFreshCoordinate.lean`.
  Only a P1-specific strengthening could close the predecessor branch.

Part 3 (P1 arithmetic): the exact predecessor constants used by the Lean
  file: pairwise intersections >= 2T-N = 111848108 > 0; the absorption
  premise is NOT forced (3T <= 2N + k - 1); the collinear two-cover floor
  ceil((3T-N)/2) = 352321537 >= k = 2^28, i.e. a collinear shared triple
  forces a joint pencil with beyond-unique-decoding agreement.

Deterministic, dependency-free, runtime well under a second.
"""

from __future__ import annotations

import itertools
from fractions import Fraction


# ----------------------------------------------------------------------
# small prime field helpers
# ----------------------------------------------------------------------

def inv(a: int, p: int) -> int:
    return pow(a, p - 2, p)


def poly_eval(coeffs: list[int], x: int, p: int) -> int:
    """coeffs[j] is the coefficient of X^j."""
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def interpolate_deg1(x0: int, y0: int, x1: int, y1: int, p: int) -> list[int]:
    """The unique degree-<2 polynomial through (x0,y0),(x1,y1)."""
    slope = (y1 - y0) * inv(x1 - x0, p) % p
    return [(y0 - slope * x0) % p, slope]


def explainable(u: list[int], S: list[int], domain: list[int], k: int,
                p: int) -> bool:
    """Is there a degree-<k polynomial agreeing with u on S?"""
    if len(S) <= k:
        return True
    assert k == 2, "probe only needs k = 2"
    a, b = S[0], S[1]
    L = interpolate_deg1(domain[a], u[a], domain[b], u[b], p)
    return all(poly_eval(L, domain[e], p) == u[e] for e in S)


# ----------------------------------------------------------------------
# Part 2: explicit RS[8,2]/F_11 shared-fresh-triple countermodel
# ----------------------------------------------------------------------

P = 11
N_SMALL = 8
K_SMALL = 2
THRESH = 4                      # (1 - 1/2) * 8
DOMAIN = list(range(8))         # x_e = e in F_11

Q0 = [1, 2]                     # q0(x) = 1 + 2x
Q1 = [3, 1]                     # q1(x) = 3 + x
J = [0, 1, 2, 3]
I_SHARED = 4
A_VAL, B_VAL = 1, 1             # (u0(4), u1(4)); != (q0(4), q1(4)) = (9, 7)
GAMMAS = [1, 2, 3]
WITNESS = [[0, 4, 5, 6], [1, 4, 5, 7], [2, 4, 6, 7]]
J_ANCHOR = [0, 1, 2]            # the single J-coordinate of each witness


def build_countermodel():
    p = P
    u0 = [None] * N_SMALL
    u1 = [None] * N_SMALL
    for e in J:
        u0[e] = poly_eval(Q0, DOMAIN[e], p)
        u1[e] = poly_eval(Q1, DOMAIN[e], p)
    u0[I_SHARED], u1[I_SHARED] = A_VAL, B_VAL

    # witness codewords: through the J anchor (line value there) and the
    # shared coordinate value a + gamma*b
    lines = []
    for j, g in enumerate(GAMMAS):
        c = J_ANCHOR[j]
        y_anchor = (u0[c] + g * u1[c]) % p
        y_shared = (A_VAL + g * B_VAL) % p
        lines.append(interpolate_deg1(DOMAIN[c], y_anchor,
                                      DOMAIN[I_SHARED], y_shared, p))

    # solve the doubly-used outside coordinates 5, 6, 7
    shared_pairs = {5: (0, 1), 6: (0, 2), 7: (1, 2)}
    for e, (ja, jb) in shared_pairs.items():
        ga, gb = GAMMAS[ja], GAMMAS[jb]
        ya = poly_eval(lines[ja], DOMAIN[e], p)
        yb = poly_eval(lines[jb], DOMAIN[e], p)
        u1[e] = (yb - ya) * inv(gb - ga, p) % p
        u0[e] = (ya - ga * u1[e]) % p
    return u0, u1, lines


def check_countermodel(u0, u1, lines) -> None:
    p = P
    # (a) joint pair on J
    for e in J:
        assert poly_eval(Q0, DOMAIN[e], p) == u0[e]
        assert poly_eval(Q1, DOMAIN[e], p) == u1[e]
    # (b) i not in the maximal joint set of (q0, q1)
    assert (poly_eval(Q0, I_SHARED, p), poly_eval(Q1, I_SHARED, p)) != \
        (u0[I_SHARED], u1[I_SHARED])
    maximal_joint = [e for e in range(N_SMALL)
                     if poly_eval(Q0, DOMAIN[e], p) == u0[e]
                     and poly_eval(Q1, DOMAIN[e], p) == u1[e]]
    assert I_SHARED not in maximal_joint
    # (c) each witness: line agreement + threshold size + shared coordinate
    for j, g in enumerate(GAMMAS):
        S = WITNESS[j]
        assert len(S) == THRESH and I_SHARED in S and I_SHARED not in J
        for e in S:
            assert poly_eval(lines[j], DOMAIN[e], p) == \
                (u0[e] + g * u1[e]) % p
    # (d) non-jointness on each witness: the u0 row is unexplainable
    #     (this is the certificate shape transcribed into Lean)
    for j in range(3):
        S = WITNESS[j]
        assert not explainable(u0, S, DOMAIN, K_SMALL, p), \
            f"u0 explainable on witness {j}; countermodel broken"
    # (e) structural laws on the instance
    # distinct values at the shared coordinate (u1(4) = 1 != 0)
    vals = [poly_eval(lines[j], I_SHARED, p) for j in range(3)]
    assert len(set(vals)) == 3
    # pairwise pencils agree with the stack on the pairwise intersections
    for ja, jb in itertools.combinations(range(3), 2):
        ga, gb = GAMMAS[ja], GAMMAS[jb]
        w1 = [(lines[jb][t] - lines[ja][t]) * inv(gb - ga, p) % p
              for t in range(2)]
        w0 = [(lines[ja][t] - ga * w1[t]) % p for t in range(2)]
        inter = sorted(set(WITNESS[ja]) & set(WITNESS[jb]))
        assert inter, "pairwise intersection unexpectedly empty"
        for e in inter:
            assert poly_eval(w0, DOMAIN[e], p) == u0[e]
            assert poly_eval(w1, DOMAIN[e], p) == u1[e]
        # incomparability
        assert not set(WITNESS[ja]) <= set(WITNESS[jb])
        assert not set(WITNESS[jb]) <= set(WITNESS[ja])
        # absorption dichotomy premise fails here, as it must
        assert len(set(WITNESS[ja]) & set(WITNESS[jb]) & set(J)) < K_SMALL
    # non-collinearity: the three witness codewords are NOT on one pencil
    g1, g2, g3 = GAMMAS
    w1 = [(lines[1][t] - lines[0][t]) * inv(g2 - g1, p) % p for t in range(2)]
    w0 = [(lines[0][t] - g1 * w1[t]) % p for t in range(2)]
    pred3 = [(w0[t] + g3 * w1[t]) % p for t in range(2)]
    collinear = pred3 == lines[2]
    # two-cover bound
    U = sorted((set(WITNESS[0]) & set(WITNESS[1]))
               | (set(WITNESS[0]) & set(WITNESS[2]))
               | (set(WITNESS[1]) & set(WITNESS[2])))
    assert sum(len(S) for S in WITNESS) <= N_SMALL + 2 * len(U)
    print("countermodel over F_11 verified:")
    print(f"  u0 = {u0}")
    print(f"  u1 = {u1}")
    print(f"  witness codewords (const, slope) = {lines}")
    print(f"  maximal joint set of (q0,q1) = {maximal_joint}")
    print(f"  shared coordinate {I_SHARED} not in it; values at it: {vals}")
    print(f"  triple collinear: {collinear}")
    print(f"  two-cover region U = {U}")


# ----------------------------------------------------------------------
# Part 1: randomized structural-law verification on generic RS instances
# ----------------------------------------------------------------------

def lcg(state: int):
    while True:
        state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
        yield state >> 33


def random_structural_checks() -> None:
    """Regression-test the divided-difference pencil on 5000 deterministic
    pseudorandom RS[8,2]/F_11 witness-pair attempts."""
    p = P
    rng = lcg(20260710)
    checked_pencil = checked_large_intersection = 0
    for _ in range(5000):
        g1, g2 = (next(rng) % (p - 1)) + 1, (next(rng) % (p - 1)) + 1
        if g1 == g2:
            continue
        p1 = [next(rng) % p, next(rng) % p]
        p2 = [next(rng) % p, next(rng) % p]
        u1 = [next(rng) % p for _ in range(N_SMALL)]
        S1 = sorted(next(rng) % N_SMALL for _ in range(5))
        S2 = sorted(next(rng) % N_SMALL for _ in range(5))
        # define u0 so that both witnesses agree on their sets
        u0 = [next(rng) % p for _ in range(N_SMALL)]
        for e in set(S1):
            u0[e] = (poly_eval(p1, DOMAIN[e], p) - g1 * u1[e]) % p
        for e in set(S2):
            want = (poly_eval(p2, DOMAIN[e], p) - g2 * u1[e]) % p
            if e in set(S1):
                # overconstrained coordinate: adjust u1 instead
                num = (poly_eval(p2, DOMAIN[e], p)
                       - poly_eval(p1, DOMAIN[e], p)) % p
                u1[e] = num * inv(g2 - g1, p) % p
                u0[e] = (poly_eval(p1, DOMAIN[e], p) - g1 * u1[e]) % p
            else:
                u0[e] = want
        # pencil law
        w1 = [(p2[t] - p1[t]) * inv(g2 - g1, p) % p for t in range(2)]
        w0 = [(p1[t] - g1 * w1[t]) % p for t in range(2)]
        for e in set(S1) & set(S2):
            assert poly_eval(w0, DOMAIN[e], p) == u0[e]
            assert poly_eval(w1, DOMAIN[e], p) == u1[e]
        checked_pencil += 1
        # Count large intersections for coverage.  Since the reference pair
        # here is defined to be the derived pencil itself, this is not an
        # independent test of the absorption/uniqueness argument.
        inter = set(S1) & set(S2)
        if len(inter) >= K_SMALL:
            for e in inter:
                assert poly_eval(w0, DOMAIN[e], p) == u0[e]
            checked_large_intersection += 1
    print(f"random pencil law checks passed: {checked_pencil} "
          f"(large-intersection cases: {checked_large_intersection})")


# ----------------------------------------------------------------------
# Part 3: exact P1 predecessor arithmetic
# ----------------------------------------------------------------------

def p1_arithmetic() -> None:
    N = 2**30
    k = 2**28
    T = 592794966            # predecessorThreshold
    assert N - T == 480946858
    assert 2 * T - N == 111848108, "pairwise-intersection floor"
    # absorption premise NOT forced: witnesses can miss J beyond k-1
    assert 3 * T <= 2 * N + k - 1, "triple-J overlap can be < k"
    assert 3 * T - 2 * N < 0     # even the naive floor is negative
    # collinear boost: two-cover floor >= k
    two_cover_floor = -((-(3 * T - N)) // 2)  # ceil((3T-N)/2)
    assert 3 * T - N == 704643074
    assert two_cover_floor == 352321537
    assert two_cover_floor >= k
    print("P1 arithmetic verified:")
    print(f"  2T-N = {2*T-N} (pairwise intersection floor, positive)")
    print(f"  3T-2N = {3*T-2*N} (absorption premise not forced)")
    print(f"  ceil((3T-N)/2) = {two_cover_floor} >= k = {k} "
          f"(collinear shared triple forces a joint pencil with "
          f"beyond-unique-decoding agreement)")
    print(f"  ratio to threshold: {Fraction(two_cover_floor, T)} < 1 "
          f"(so even collinearity does not contradict non-jointness)")


def main() -> None:
    u0, u1, lines = build_countermodel()
    check_countermodel(u0, u1, lines)
    random_structural_checks()
    p1_arithmetic()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
