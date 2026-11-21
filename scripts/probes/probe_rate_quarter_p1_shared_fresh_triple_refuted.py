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


def _require(condition: bool, detail: str) -> None:
    """Keep certificate checks active under Python optimization flags."""
    if not condition:
        raise AssertionError(detail)


def part1_midscale() -> None:
    p, n, m, k = 257, 256, 16, 64
    t_mid = -(-T * n // N)  # ceil(T * n / N) = 142
    _require(t_mid == 142, "midscale threshold is not 142")
    g = 3
    _require(
        pow(g, n, p) == 1 and pow(g, n // 2, p) != 1,
        "midscale generator does not have order 256",
    )
    omega = pow(g, m, p)
    _require(
        pow(omega, 16, p) == 1 and pow(omega, 8, p) != 1,
        "midscale omega does not have order 16",
    )
    gammas = [(-pow(omega, 2 * j, p)) % p for j in range(3)]
    _require(len(set(gammas)) == 3, "midscale gammas are not distinct")

    def residue(e: int) -> int:
        return e % 16

    u0 = [pow(g, e * (n // 8), p) if residue(e) in OIDX else 0
          for e in range(n)]
    # (g^e)^(2m) with 2m = n/8 = 32 at this scale
    u1 = [1 if residue(e) in OIDX else 0 for e in range(n)]
    S = [[e for e in range(n) if residue(e) in SIDX[j]] for j in range(3)]
    J = [e for e in range(n) if residue(e) in JIDX]
    _require(len(J) == 9 * m >= t_mid, "joint set has the wrong size")
    for j in range(3):
        _require(len(S[j]) == 9 * m >= t_mid, f"S_{j} has the wrong size")
    # agreement: p_j(x) = x^(2m) + gamma_j on S_j
    for j in range(3):
        for e in S[j]:
            x = pow(g, e, p)
            line = (u0[e] + gammas[j] * u1[e]) % p
            _require(
                (pow(x, 2 * m, p) + gammas[j]) % p == line,
                f"line agreement failed for gamma {j} at point {e}",
            )
    # joint pair (0,0) on J
    _require(
        all(u0[e] == 0 and u1[e] == 0 for e in J),
        "the joint pair does not vanish on J",
    )
    # non-jointness of the u1 row on each S_j: the unique deg-<k candidate
    # through the O-part is the constant 1 (>= k points), mismatch on J-part
    for j in range(3):
        opart = [e for e in S[j] if residue(e) in OIDX]
        jpart = [e for e in S[j] if residue(e) not in OIDX]
        _require(
            len(opart) == 7 * m >= k and bool(jpart),
            f"S_{j} does not have the required O-part and J-part sizes",
        )
        _require(all(u1[e] == 1 for e in opart), f"u1 is not one on O-part of S_{j}")
        _require(all(u1[e] == 0 for e in jpart), f"u1 is not zero on J-part of S_{j}")
    # shared fresh coordinate
    i = I_RESIDUE
    _require(
        all(i in S[j] for j in range(3)) and i not in J,
        "fresh coordinate is not shared across all S_j outside J",
    )
    # bonus: i is not even in the maximal joint set of (0,0)
    _require(u1[i] != 0, "fresh coordinate is in the maximal joint set")
    print(f"part 1 (mu_256 / F_257, k=64, T={t_mid}): all clauses verified")


def part2_literal_p1() -> None:
    m = 2**26
    omega = pow(G, m, P)
    _require(
        pow(G, N, P) == 1 and pow(G, N // 2, P) != 1,
        "literal P1 generator does not have order 2^30",
    )
    _require(
        pow(omega, 16, P) == 1 and pow(omega, 8, P) != 1,
        "literal P1 omega does not have order 16",
    )
    gammas = [(-pow(omega, 2 * j, P)) % P for j in range(3)]
    _require(len(set(gammas)) == 3, "literal P1 gammas are not distinct")
    # per-residue line identity: omega^(2t) + gamma_j = 0 iff t in pair(j)
    for j in range(3):
        zeros = [t for t in range(16)
                 if (pow(omega, 2 * t, P) + gammas[j]) % P == 0]
        _require(
            zeros == sorted([j, j + 8]),
            f"literal P1 zero residues for gamma {j} are {zeros}",
        )
    # coset-level agreement identity (g^e)^(2^27) = omega^(2*(e mod 16))
    for t in range(16):
        e = 16 * 12345 + t  # arbitrary representative
        _require(
            pow(pow(G, e, P), 2**27, P) == pow(omega, 2 * t, P),
            f"coset identity failed at residue {t}",
        )
    # thresholds and shape
    _require(9 * m == 603979776 >= T, "literal P1 joint and agreement sets are too small")
    _require(7 * m == 469762048 >= K, "literal P1 O-part does not pin the u1 row")
    _require(2**27 < K, "literal P1 witness polynomial degree is too large")
    _require(
        JIDX + OIDX and sorted(JIDX + OIDX) == list(range(16)),
        "J and O residue classes do not partition the domain",
    )
    _require(
        all(set(s) <= set(range(16)) and len(s) == 9 for s in SIDX),
        "an agreement set has invalid residue classes",
    )
    _require(
        all(I_RESIDUE in s for s in SIDX) and I_RESIDUE not in JIDX,
        "fresh residue is not shared outside the joint set",
    )
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
