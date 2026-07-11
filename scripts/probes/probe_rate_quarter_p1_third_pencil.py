r"""Third pencil through a base scalar: exclusion fails, cap 2 is refuted.

Successor of `probe_rate_quarter_p1_pencil_count_charge.py`.  The fiber
consumer closes the prize budget when at most TWO divided-difference pencils
pass through a base scalar (`BasePencilImageCap`).  This probe shows the cap
is FALSE at the P1 shape, by the partners-collinear trick:

    put the three partners on one pencil sigma = (x^(2m), 1):
        p_j = x^(2m) + gamma_j,   j = 1,2,3,
    and take the base witness OFF sigma:
        p_0 = x^(2m) + x^m.
    Then the three pair pencils pi_j = pencil(gamma_0, gamma_j) are pairwise
    distinct automatically (pi_i = pi_j would force p_0 onto sigma), and

        dir_j = (gamma_j - x^m)/(gamma_j - gamma_0),
        base_j = p_0 - gamma_0 * dir_j,
        dir_i - dir_j  proportional to  (x^m - gamma_0),

    which never vanishes when gamma_0 is not a 32nd root of unity.

Class design (m-fold, 32 residue classes):
    B  = {0..13}   : u = (x^(2m), 1)            (sigma-aligned, 14 classes)
    P1 = {14..23}  : u = (base_1, dir_1) values (pi_1-aligned, 10 classes)
    P2 = {24..27}  : u = (base_2, dir_2) values (pi_2-aligned, 4 classes)
    P3 = {28..31}  : u = (base_3, dir_3) values (pi_3-aligned, 4 classes)
    S0 = P1+P2+P3 (18 classes), S_j = B + (4 classes of P_j) (18 classes).

Non-jointness is pinning-certified: partners' second row is pinned to the
constant 1 by the 14 >= k/m classes of B, mismatching on P_j (dir_j != 1
since x^m != gamma_0); the base's second row is pinned to dir_1 by the
10 >= k/m classes of P1, mismatching on P2 (dir_1 != dir_2, same reason).

Part 1 verifies everything by full enumeration at mu_256/F_257 (m = 8,
k = 64, T = 142), including image card = 3 through the base.  Part 2 checks
the literal-P1 constants (m = 2^25, 32 classes of 2^25): 18 classes >= T,
14 and 10 classes >= k, and gamma_0 = 2 is not a 32nd root of unity in F_P.
The Lean transcription is `_P1RateQuarterThirdPencilExclusion.lean`, which
refutes `BasePencilImageCap` at the literal canonical P1 domain.

Deterministic, dependency-free, runtime under a second.
"""

from __future__ import annotations

P_SMALL = 257
N_SMALL = 256
K_SMALL = 64
T_SMALL = 142

P = 365375409332725729550921208179070755120141565953
G_P1 = 303645430271030343624574566109998498685964493478
N = 2**30
K = 2**28
T = 592794966

B_CL = list(range(0, 14))
P1_CL = list(range(14, 24))
P2_CL = list(range(24, 28))
P3_CL = list(range(28, 32))
# gamma_0 must lie outside mu_32 of the working field: 2 at literal P1
# (2^32 != 1 mod P), but 3 (a generator) at the mu_256/F_257 mid-scale.


def inv(a, p=P_SMALL):
    return pow(a, p - 2, p)


def interpolate(pts, p=P_SMALL):
    n = len(pts)
    coeffs = [0] * n
    for i, (xi, yi) in enumerate(pts):
        num = [1]
        den = 1
        for jj, (xj, _) in enumerate(pts):
            if jj != i:
                new = [0] + num
                for t in range(len(num)):
                    new[t] = (new[t] - xj * num[t]) % p
                num = new
                den = den * (xi - xj) % p
        scale = yi * inv(den) % p
        while len(coeffs) < len(num):
            coeffs.append(0)
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + scale * num[t]) % p
    return coeffs


def pval(c, x, p=P_SMALL):
    acc = 0
    for cc in reversed(c):
        acc = (acc * x + cc) % p
    return acc


def explainable(u, S, dom, k, p=P_SMALL):
    if len(S) <= k:
        return True
    L = interpolate([(dom[e], u[e]) for e in S[:k]], p)
    return all(pval(L, dom[e], p) == u[e] for e in S[k:])


def part1_midscale():
    p, n, m = P_SMALL, N_SMALL, 8
    g = 3
    dom = [pow(g, e, p) for e in range(n)]
    G0, G1, G2, G3 = 3, 1, 2, 4
    assert pow(G0, 32, p) != 1, "gamma_0 must not be a 32nd root of unity"

    def xm(x):
        return pow(x, m, p)

    def x2m(x):
        return pow(x, 2 * m, p)

    gammas = [G0, G1, G2, G3]
    pfun = [[(x2m(x) + xm(x)) % p for x in dom]]           # p0 off sigma
    for gj in (G1, G2, G3):
        pfun.append([(x2m(x) + gj) % p for x in dom])      # partners on sigma

    def dirj(j, x):
        return (gammas[j] - xm(x)) * inv(gammas[j] - G0, p) % p

    def basej(j, x):
        return (pfun[0][dom.index(x)] - G0 * dirj(j, x)) % p

    u0 = [0] * n
    u1 = [0] * n
    for e in range(n):
        x, cl = dom[e], e % 32
        if cl in B_CL:
            u0[e], u1[e] = x2m(x), 1
        elif cl in P1_CL:
            u0[e], u1[e] = basej(1, x), dirj(1, x)
        elif cl in P2_CL:
            u0[e], u1[e] = basej(2, x), dirj(2, x)
        else:
            u0[e], u1[e] = basej(3, x), dirj(3, x)
    Scl = [P1_CL + P2_CL + P3_CL,
           B_CL + P1_CL[:4], B_CL + P2_CL, B_CL + P3_CL]
    S = [[e for e in range(n) if e % 32 in Scl[j]] for j in range(4)]
    for j in range(4):
        assert len(S[j]) == 18 * m == 144 >= T_SMALL
        for e in S[j]:
            assert pfun[j][e] == (u0[e] + gammas[j] * u1[e]) % p, (j, e)
    # non-jointness: pinning certificates
    for j in range(4):
        e0 = not explainable(u0, S[j], dom, K_SMALL)
        e1 = not explainable(u1, S[j], dom, K_SMALL)
        assert e0 or e1, f"witness {j} jointly explainable"
    # the second-row certificates used in Lean: pinning blocks >= k
    assert 14 * m >= K_SMALL and 10 * m >= K_SMALL
    for x in [dom[e] for e in range(n) if e % 32 in P1_CL]:
        assert dirj(1, x) != 1                # partners' mismatch on P_j
    for x in [dom[e] for e in range(n) if e % 32 in P2_CL]:
        assert dirj(1, x) != dirj(2, x)       # base's mismatch on P2
    # three distinct pencils through the base
    pencils = set()
    for j in (1, 2, 3):
        w1 = [(pfun[j][e] - pfun[0][e]) * inv(gammas[j] - G0, p) % p
              for e in range(n)]
        w0 = [(pfun[0][e] - G0 * w1[e]) % p for e in range(n)]
        pencils.add((tuple(w0), tuple(w1)))
        # sanity: w1 matches dir_j pointwise
        for e in range(n):
            assert w1[e] == dirj(j, dom[e])
    assert len(pencils) == 3, "expected three distinct pencils"
    print("part 1 verified: THREE distinct pencils through one base scalar "
          "at the P1 shape (mu_256/F_257); BasePencilImageCap(2) refuted "
          "at shape")


def part2_literal_p1():
    m = 2**25
    assert 32 * m == N
    assert 18 * m == 603979776 >= T          # witness thresholds
    assert 14 * m == 469762048 >= K          # partners' pinning block B
    assert 10 * m == 335544320 >= K          # base's pinning block P1
    assert 4 * m == 134217728 >= 2 * T - N   # pairwise floors (context)
    assert 2 * m < K                          # sigma direction degree x^(2m)
    # gamma_0 = 2 is not a 32nd root of unity mod P: 2^32 - 1 not divisible
    assert pow(2, 32, P) != 1
    assert P > 2**32 - 1
    # omega32 = g^(2^25) has order 32
    om = pow(G_P1, m, P)
    assert pow(om, 32, P) == 1 and pow(om, 16, P) != 1
    # dir difference identity: dir_i - dir_j prop to (x^m - gamma_0), never 0
    for t in range(32):
        x = pow(om, t, P)
        assert x != 2
    print("part 2 verified: literal P1 constants for the m = 2^25 fold")


def main():
    part1_midscale()
    part2_literal_p1()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
