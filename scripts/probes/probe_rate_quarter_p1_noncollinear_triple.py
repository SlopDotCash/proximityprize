#!/usr/bin/env python3
r"""Non-collinear shared-fresh triple at the P1 predecessor shape.

Successor of `probe_rate_quarter_p1_shared_fresh_coordinate.py`.  The pencil
rigidity theorem (formalized in `_P1RateQuarterNonCollinearTriple.lean`) says:
if three threshold witnesses of distinct bad scalars overlap in >= k common
coordinates, their witness codewords are forced onto ONE pencil (collinear),
and the collinear boost then produces a joint pencil with two-cover agreement
>= ceil((3T-N)/2) >= k.  At the literal P1 predecessor the rigidity premise is
NOT forced:

    3T - 2N = -369098750 < 0  (so the triple-overlap floor is vacuous).

This probe shows the non-collinear escape is REAL at the exact P1 inequality
shape.  Working parameters n = 32, k = 8, T = 18 over F_37 satisfy the four
shape inequalities of the P1 predecessor:

    2T - n = 4 > 0        (pairwise witness intersections forced nonempty)
    3T - 2n = -10 < 0     (triple intersection NOT forced; rigidity escapable)
    2T <= n + k - 1       (witnesses can miss the joint set beyond k-1)
    k / n = 1/4,  T / n = 0.5625 ~ 0.552  (rate-quarter, predecessor radius)

Construction: fix the joint pair (q0,q1) and J = {0..17}; take
p1 = (q0+g1*q1) + c1*A1, p2 = (q0+g2*q2) + c2*A2, p3 = q0+g3*q1, where
A1, A2 are degree-7 products of distinct J-linear factors chosen so that
B = A1 + r*A2 has >= 5 distinct roots inside O = {18..31}.  Those roots are
the triple-overlap coordinates; the second divided difference of (p1,p2,p3)
is a nonzero multiple of B, so it vanishes there (consistency of the shared
stack values) but not identically: the triple is NON-collinear.  The search
for (A1, A2, r) uses the exact collision statistic r_t = -A1(t)/A2(t).

Everything is then verified literally: threshold witnesses, line agreements,
row-unexplainability certificates (deg-<8 interpolant + mismatch), the joint
set J, the shared fresh coordinate, non-absorption, and non-collinearity.
The printed certificate is transcribed into
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterNonCollinearTriple.lean`.

Deterministic, dependency-free, runtime a few seconds.
"""

from __future__ import annotations

import itertools

Q = 37
N_SMALL = 32
K_SMALL = 8
T_SMALL = 18
DOMAIN = list(range(32))
J = list(range(18))
O = list(range(18, 32))
GAMMAS = [1, 2, 3]

Q0 = [1, 1, 0, 0, 0, 0, 0, 0]        # q0(x) = 1 + x
Q1 = [2, 0, 0, 1, 0, 0, 0, 0]        # q1(x) = 2 + x^3


def inv(a: int) -> int:
    return pow(a, Q - 2, Q)


def pval(c: list[int], x: int) -> int:
    acc = 0
    for cc in reversed(c):
        acc = (acc * x + cc) % Q
    return acc


def padd(a, b):
    m = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % Q
            for i in range(m)]


def pscale(s, a):
    return [s * c % Q for c in a]


def prod_linear(roots: list[int]) -> list[int]:
    c = [1]
    for r in roots:
        c = [0] + c
        for i in range(len(c) - 1):
            c[i] = (c[i] - r * c[i + 1]) % Q
    return c


def interpolate(pts: list[tuple[int, int]]) -> list[int]:
    """Lagrange interpolation, degree < len(pts)."""
    n = len(pts)
    coeffs = [0] * n
    for i, (xi, yi) in enumerate(pts):
        num = [1]
        den = 1
        for j, (xj, _) in enumerate(pts):
            if j != i:
                num = padd([(-xj) * c % Q for c in num], [0] + num)
                den = den * (xi - xj) % Q
        coeffs = padd(coeffs, pscale(yi * inv(den) % Q, num))
    return coeffs


def lcg(state: int):
    while True:
        state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
        yield state >> 33


def search_A_pair():
    """Find 7-subsets A1 != A2 of J and r with >= 5 collisions of
    r_t = -A1(t)/A2(t) over t in O."""
    rng = lcg(20260710)
    for _ in range(200000):
        A1 = sorted({next(rng) % 18 for _ in range(10)})[:7]
        A2 = sorted({next(rng) % 18 for _ in range(10)})[:7]
        if len(A1) < 7 or len(A2) < 7 or A1 == A2:
            continue
        a1c, a2c = prod_linear(A1), prod_linear(A2)
        hist: dict[int, list[int]] = {}
        for t in O:
            v2 = pval(a2c, t)
            if v2 == 0:
                continue
            r = (-pval(a1c, t)) * inv(v2) % Q
            hist.setdefault(r, []).append(t)
        for r, ts in hist.items():
            if r != 0 and len(ts) >= 5:
                return A1, A2, r, ts[:5]
    raise RuntimeError("no collision found")


def build():
    A1roots, A2roots, r, triple = search_A_pair()
    g1, g2, g3 = GAMMAS
    a1c, a2c = prod_linear(A1roots), prod_linear(A2roots)
    # second divided difference D = (g3-g2)c1 A1 - (g3-g1)c2 A2 = lam*B
    c1 = inv(g3 - g2)
    c2 = (-r) * inv(g3 - g1) % Q
    qline = [padd(Q0, pscale(g, Q1)) for g in GAMMAS]
    p1 = padd(qline[0], pscale(c1, a1c))
    p2 = padd(qline[1], pscale(c2, a2c))
    p3 = qline[2]
    lines = [p1, p2, p3]
    # witness sets
    SJ = [A1roots, A2roots, list(range(7))]
    rest = [t for t in O if t not in triple]
    P12, P13, P23 = rest[0:3], rest[3:6], rest[6:9]
    SO = [triple + P12 + P13, triple + P12 + P23, triple + P13 + P23]
    S = [sorted(SJ[j] + SO[j]) for j in range(3)]
    # received stack
    u0 = [None] * N_SMALL
    u1 = [None] * N_SMALL
    for e in J:
        u0[e] = pval(Q0, e)
        u1[e] = pval(Q1, e)
    pair_of = {tuple(sorted(P12)): (0, 1), tuple(sorted(P13)): (0, 2),
               tuple(sorted(P23)): (1, 2)}
    for block, (ja, jb) in pair_of.items():
        ga, gb = GAMMAS[ja], GAMMAS[jb]
        for e in block:
            ya, yb = pval(lines[ja], e), pval(lines[jb], e)
            u1[e] = (yb - ya) * inv(gb - ga) % Q
            u0[e] = (ya - ga * u1[e]) % Q
    for e in triple:
        ya, yb = pval(lines[0], e), pval(lines[1], e)
        u1[e] = (yb - ya) * inv(g2 - g1) % Q
        u0[e] = (ya - g1 * u1[e]) % Q
    return dict(A1=A1roots, A2=A2roots, r=r, triple=triple, lines=lines,
                S=S, u0=u0, u1=u1, c1=c1, c2=c2)


def row_certificate(u, Sj):
    """Interpolant through the first 8 points of Sj + a mismatch point,
    or None if the row is degree-<8 explainable on Sj."""
    core = Sj[:K_SMALL]
    L = interpolate([(e, u[e]) for e in core])
    for e in Sj[K_SMALL:]:
        if pval(L, e) != u[e]:
            return core, L, e
    return None


def check(cert) -> None:
    S, lines, u0, u1 = cert["S"], cert["lines"], cert["u0"], cert["u1"]
    triple = cert["triple"]
    g1, g2, g3 = GAMMAS
    # P1 shape
    assert 2 * T_SMALL - N_SMALL > 0
    assert 3 * T_SMALL - 2 * N_SMALL < 0
    assert 2 * T_SMALL <= N_SMALL + K_SMALL - 1
    assert 4 * K_SMALL == N_SMALL
    # literal P1: rigidity premise not forced
    T, N, k = 592794966, 2**30, 2**28
    assert 3 * T - 2 * N == -369098750 < 0 and not (3 * T - 2 * N >= k)
    # witnesses
    for j, g in enumerate(GAMMAS):
        assert len(S[j]) == T_SMALL
        for e in S[j]:
            assert pval(lines[j], e) == (u0[e] + g * u1[e]) % Q, (j, e)
    # joint set
    for e in J:
        assert pval(Q0, e) == u0[e] and pval(Q1, e) == u1[e]
    # shared fresh coordinate: first triple point
    i = triple[0]
    assert all(i in S[j] for j in range(3)) and i not in J
    # triple overlap below k (rigidity escape) yet all of `triple` is common
    common = set(S[0]) & set(S[1]) & set(S[2])
    assert set(triple) <= common and len(common) < K_SMALL
    # non-absorption: u and (q0,q1) differ at i, and in the u0 row
    assert pval(Q0, i) != u0[i], "need first-row mismatch for the Lean cert"
    # NON-collinearity: predicted p3 from the (1,2) pencil differs from p3
    w1 = [(cb - ca) * inv(g2 - g1) % Q
          for ca, cb in itertools.zip_longest(lines[0], lines[1],
                                              fillvalue=0)]
    w0 = [(ca - g1 * wb) % Q
          for ca, wb in itertools.zip_longest(lines[0], w1, fillvalue=0)]
    pred3 = [(a + g3 * b) % Q
             for a, b in itertools.zip_longest(w0, w1, fillvalue=0)]
    mismatches = [x for x in DOMAIN if pval(pred3, x) != pval(lines[2], x)]
    assert mismatches, "triple unexpectedly collinear"
    # but the pencil prediction DOES hold on the triple overlap
    for t in triple:
        assert pval(pred3, t) == pval(lines[2], t)
    # row-unexplainability certificates (u0 row) for each witness
    certs = []
    for j in range(3):
        rc = row_certificate(u0, S[j])
        assert rc is not None, f"u0 row explainable on witness {j}"
        certs.append(rc)
    # non-absorption certificate: u0 = q0 on J, q0 mismatch at i
    assert all(pval(Q0, e) == u0[e] for e in J[:K_SMALL])
    print("NON-COLLINEAR shared-fresh triple at P1 shape verified (F_37):")
    print(f"  A1 roots = {cert['A1']}, A2 roots = {cert['A2']}, "
          f"r = {cert['r']}")
    print(f"  c1 = {cert['c1']}, c2 = {cert['c2']}")
    print(f"  triple overlap = {triple} (|common| = {len(common)} < k = 8)")
    print(f"  witnesses = {S}")
    print(f"  u0 = {u0}")
    print(f"  u1 = {u1}")
    print(f"  witness polys (coeff, low->high) = {lines}")
    print(f"  shared fresh i = {i}; q0(i) = {pval(Q0, i)} != u0(i) = {u0[i]}")
    print(f"  non-collinearity witnesses (pred3 != p3 at) = {mismatches}")
    print("  row certificates (core, interpolant, mismatch):")
    for j, (core, L, e) in enumerate(certs):
        print(f"    S{j+1}: core = {core}, L = {L}, mismatch at {e} "
              f"(L(e) = {pval(L, e)}, u0(e) = {u0[e]})")


def main() -> None:
    cert = build()
    check(cert)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
