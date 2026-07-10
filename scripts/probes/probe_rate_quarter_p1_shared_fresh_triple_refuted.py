#!/usr/bin/env python3
r"""P1-scale refutation of SharedFreshTripleFree: the coset construction.

Successor of `probe_rate_quarter_p1_noncollinear_triple.py`.  The
shared-fresh-triple residual `SharedFreshTripleFree` (no fresh coordinate
outside a threshold joint set carries three distinct bad scalars at the P1
predecessor) is refuted CONSTRUCTIVELY on the literal smooth domain
mu_{2^30} in F_P by a purely generator-symbolic certificate.

Construction (m = 2^26, y = x^m maps mu_{2^30} onto mu_16 = <omega>,
omega = g^(2^26)):

    residue classes t = e mod 16 of the power enumeration e -> g^e;
    JIdx = {0,1,2,3,4,8,9,10,11}  (9 cosets, |J| = 9*2^26 >= T),
    OIdx = {5,6,7,12,13,14,15}    (7 cosets),
    u0(e) = (g^e)^(2^27) and u1(e) = 1 on O-cosets; u0 = u1 = 0 on J-cosets;
    gamma_j = -omega^(2(j-1)) for j = 1,2,3;
    p_j(X) = X^(2^27) + gamma_j  (degree 2^27 < k = 2^28);
    S_j = O-cosets + the two cosets {j-1, j-1+8}   (9 cosets >= T).

Clauses:
  * (0,0) jointly explains J (u vanishes there);
  * p_j agrees with the line on S_j: on O-cosets by definition, on the two
    J-cosets because omega^(2t) = -gamma_j exactly for t = j-1, j-1+8;
  * non-jointness: any degree-<k explanation of the u1 row agrees with the
    constant 1 on the 7*2^26 >= k O-part points, hence equals 1, but
    u1 = 0 on the J-part of S_j;
  * the fresh coordinate i = 5 (residue 5) lies in every S_j and outside J.

Part 1 fully enumerates the identical construction at the mid-scale smooth
domain mu_256 = F_257^* (m = 16, k = 64, threshold 142 = ceil of the exact
P1 ratio).  Part 2 verifies every coset-level identity at the LITERAL P1
parameters (big-integer arithmetic in F_P, 16 residue classes).  The Lean
certificate is `_P1RateQuarterSharedFreshTripleP1Refuted.lean`; there the
whole construction is proved symbolically from `orderOf g = 2^30` alone.

Deterministic, dependency-free, runtime under a second.
"""

from __future__ import annotations

# literal P1 constants (from _PrizeShapePrimeP30.lean / the predecessor files)
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
K = 2**28
T = 592794966

JIDX = [0, 1, 2, 3, 4, 8, 9, 10, 11]
OIDX = [5, 6, 7, 12, 13, 14, 15]
SIDX = [sorted(OIDX + [0, 8]), sorted(OIDX + [1, 9]), sorted(OIDX + [2, 10])]
I_RESIDUE = 5


def part1_midscale() -> None:
    p, n, m, k = 257, 256, 16, 64
    t_mid = -(-T * n // N)  # ceil(T * n / N) = 142
    assert t_mid == 142
    g = 3
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1  # order 256
    omega = pow(g, m, p)
    assert pow(omega, 16, p) == 1 and pow(omega, 8, p) != 1
    gammas = [(-pow(omega, 2 * j, p)) % p for j in range(3)]
    assert len(set(gammas)) == 3

    def residue(e: int) -> int:
        return e % 16

    u0 = [pow(g, e * (n // 8), p) if residue(e) in OIDX else 0
          for e in range(n)]
    # (g^e)^(2m) with 2m = n/8 = 32 at this scale
    u1 = [1 if residue(e) in OIDX else 0 for e in range(n)]
    S = [[e for e in range(n) if residue(e) in SIDX[j]] for j in range(3)]
    J = [e for e in range(n) if residue(e) in JIDX]
    assert len(J) == 9 * m >= t_mid
    for j in range(3):
        assert len(S[j]) == 9 * m >= t_mid
    # agreement: p_j(x) = x^(2m) + gamma_j on S_j
    for j in range(3):
        for e in S[j]:
            x = pow(g, e, p)
            line = (u0[e] + gammas[j] * u1[e]) % p
            assert (pow(x, 2 * m, p) + gammas[j]) % p == line, (j, e)
    # joint pair (0,0) on J
    assert all(u0[e] == 0 and u1[e] == 0 for e in J)
    # non-jointness of the u1 row on each S_j: the unique deg-<k candidate
    # through the O-part is the constant 1 (>= k points), mismatch on J-part
    for j in range(3):
        opart = [e for e in S[j] if residue(e) in OIDX]
        jpart = [e for e in S[j] if residue(e) not in OIDX]
        assert len(opart) == 7 * m >= k and jpart
        assert all(u1[e] == 1 for e in opart)
        assert all(u1[e] == 0 for e in jpart)
    # shared fresh coordinate
    i = I_RESIDUE
    assert all(i in S[j] for j in range(3)) and i not in J
    # bonus: i is not even in the maximal joint set of (0,0)
    assert u1[i] != 0
    print(f"part 1 (mu_256 / F_257, k=64, T={t_mid}): all clauses verified")


def part2_literal_p1() -> None:
    m = 2**26
    omega = pow(G, m, P)
    assert pow(G, N, P) == 1 and pow(G, N // 2, P) != 1     # order 2^30
    assert pow(omega, 16, P) == 1 and pow(omega, 8, P) != 1  # order 16
    gammas = [(-pow(omega, 2 * j, P)) % P for j in range(3)]
    assert len(set(gammas)) == 3
    # per-residue line identity: omega^(2t) + gamma_j = 0 iff t in pair(j)
    for j in range(3):
        zeros = [t for t in range(16)
                 if (pow(omega, 2 * t, P) + gammas[j]) % P == 0]
        assert zeros == sorted([j, j + 8]), (j, zeros)
    # coset-level agreement identity (g^e)^(2^27) = omega^(2*(e mod 16))
    for t in range(16):
        e = 16 * 12345 + t  # arbitrary representative
        assert pow(pow(G, e, P), 2**27, P) == pow(omega, 2 * t, P)
    # thresholds and shape
    assert 9 * m == 603979776 >= T          # |J|, |S_j| >= T
    assert 7 * m == 469762048 >= K          # O-part pins the u1 row
    assert 2**27 < K                         # witness polynomial degree
    assert JIDX + OIDX and sorted(JIDX + OIDX) == list(range(16))
    assert all(set(s) <= set(range(16)) and len(s) == 9 for s in SIDX)
    assert all(I_RESIDUE in s for s in SIDX) and I_RESIDUE not in JIDX
    print("part 2 (literal P1, coset level): all identities verified")
    print(f"  omega = {omega}")
    print(f"  gammas = {gammas}")


def main() -> None:
    part1_midscale()
    part2_literal_p1()
    print("ALL CHECKS PASSED -- SharedFreshTripleFree is refuted at P1 "
          "by this construction")


if __name__ == "__main__":
    main()
