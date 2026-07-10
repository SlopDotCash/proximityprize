r"""Pencil-count charge at the P1 predecessor: vote partition and fiber caps.

Successor of `probe_rate_quarter_p1_shared_fresh_triple_refuted.py`.  With the
fixed-witness escape charge dead, the surviving route is counting bad scalars
by the divided-difference pencils their witnesses ride.

For a fixed pencil (w0, w1), a scalar gamma RIDES it when its witness
codeword is w0 + gamma*w1.  Then on the witness set,
(w0 - u0)(i) = gamma * (u1 - w1)(i), so every coordinate outside the ALIGNED
region {i : w0(i) = u0(i) and w1(i) = u1(i)} votes for at most one gamma.
Exact consequences (formalized in `_P1RateQuarterPencilCountCharge.lean`):

  * riders * (T - A) <= N - A   (A = #aligned, when A <= T);
  * riders <= N - A             (non-jointness gives >= 1 vote each);
  * uniform rider cap  riders <= N - T + 1 = 480946859;
  * alignment ladder   riders*T <= N + (riders-1)*A;
  * Johnson crossover: >= 10 riders forces A >= 539356427 and
    539356427^2 > N(k-1), while the 9-rider floor 532676609 stays below —
    heavy pencils are Johnson-packable, exactly from ten riders on;
  * fiber partition through a base scalar gamma0: #bad - 1 splits into
    per-pencil fibers of size <= N - T, hence
    #bad <= 1 + (#pencils through the base) * (N - T);
    over-budget (#bad > N) therefore forces >= 3 pencils through EVERY base;
  * four-witness pigeonhole: 4T > 2N, so any four threshold witnesses share
    a triple-covered coordinate.

Part 1 re-verifies the vote/rider bounds on the mu_256/F_257 one-pencil
refutation family.  Part 2 constructs a TWO-pencil-through-base bad family at
the same shape (mu_32 fold, m = 8): base gamma0 rides pencils
A = (x^16, 1) and B = (x^16 - x^8 + 1, x^8) with partners gamma1, gamma2 —
showing the pencil-image cap 2 of the consumer theorem is attained, i.e. the
`BasePencilImageCap` residual sits exactly on the realizability boundary.
Part 3 checks all literal-P1 constants used by the Lean file.

Deterministic, dependency-free, runtime under a second.
"""

from __future__ import annotations

P_SMALL = 257
N_SMALL = 256
K_SMALL = 64
T_SMALL = 142

# literal P1
N = 2**30
K = 2**28
T = 592794966


def inv(a: int, p: int = P_SMALL) -> int:
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


def check_pencil_bounds(u0, u1, riders, n, t_thresh, dom, tag):
    """riders: dict gamma -> (S, pfun).  All on one pencil (w0, w1)."""
    gammas = sorted(riders)
    g_a, g_b = gammas[0], gammas[1]
    pa, pb = riders[g_a][1], riders[g_b][1]
    w1 = [(pb[e] - pa[e]) * inv(g_b - g_a) % P_SMALL for e in range(n)]
    w0 = [(pa[e] - g_a * w1[e]) % P_SMALL for e in range(n)]
    for g, (S, pf) in riders.items():
        assert all(pf[e] == (w0[e] + g * w1[e]) % P_SMALL for e in range(n)), \
            f"{tag}: rider {g} not on the common pencil"
        assert len(S) >= t_thresh
        assert all(pf[e] == (u0[e] + g * u1[e]) % P_SMALL for e in S)
    aligned = [e for e in range(n) if w0[e] == u0[e] and w1[e] == u1[e]]
    A = len(aligned)
    R = len(riders)
    votes = {}
    for e in range(n):
        if e in aligned:
            continue
        d1 = (u1[e] - w1[e]) % P_SMALL
        d0 = (w0[e] - u0[e]) % P_SMALL
        if d1 != 0:
            votes.setdefault(d0 * inv(d1) % P_SMALL, []).append(e)
    # witness coverage and disjointness
    for g, (S, _) in riders.items():
        for e in S:
            assert e in aligned or e in votes.get(g, []), (tag, g, e)
    # exact bounds
    if A <= t_thresh:
        assert R * (t_thresh - A) <= n - A, tag
    assert R <= n - A, tag
    assert R * t_thresh <= n + (R - 1) * A, tag
    print(f"  {tag}: riders={R}, aligned={A}: vote bounds verified")
    return A


def part1_one_pencil():
    """The mu_256 refutation family: 3 riders on one pencil."""
    p, n, m = P_SMALL, N_SMALL, 16
    g = 3
    JIDX = [0, 1, 2, 3, 4, 8, 9, 10, 11]
    OIDX = [5, 6, 7, 12, 13, 14, 15]
    omega = pow(g, m, p)
    gam = [(-pow(omega, 2 * j, p)) % p for j in range(3)]
    u0 = [pow(g, e * 32, p) if e % 16 in OIDX else 0 for e in range(n)]
    u1 = [1 if e % 16 in OIDX else 0 for e in range(n)]
    riders = {}
    for j, gg in enumerate(gam):
        S = [e for e in range(n) if e % 16 in sorted(OIDX + [j, j + 8])]
        pf = [(pow(g, 32 * e, p) + gg) % p for e in range(n)]
        riders[gg] = (S, pf)
    A = check_pencil_bounds(u0, u1, riders, n, T_SMALL,
                            [pow(g, e, p) for e in range(n)], "one-pencil")
    assert A == 7 * m == 112
    print("part 1 verified")


def part2_two_pencils():
    """Two pencils through one base scalar, mu_32 fold (m = 8)."""
    p, n, m = P_SMALL, N_SMALL, 8
    g = 3
    dom = [pow(g, e, p) for e in range(n)]
    g0, g1, g2 = 1, 2, 3
    # class of e is e mod 32
    A_CL = list(range(0, 8))
    B_CL = list(range(8, 15))
    C_CL = list(range(15, 22))
    SOLO = [list(range(22, 25)), list(range(25, 28)), list(range(28, 32))]

    def x16(x):
        return pow(x, 16, p)

    def x8(x):
        return pow(x, 8, p)

    pfun = [
        [(x16(x) + 1) % p for x in dom],                       # p0 = x^16+1
        [(x16(x) + 2) % p for x in dom],                       # p1 = x^16+2
        [(x16(x) + 1 + 2 * x8(x)) % p for x in dom],           # p2
    ]
    # pencils: A = (x^16, 1); B = (x^16 - x^8 + 1, x^8);
    # C = pencil(p1@2, p2@3): dir = 2x^8 - 1, base = x^16 - 4x^8 + 4
    u0 = [0] * n
    u1 = [0] * n
    for e in range(n):
        x, cl = dom[e], e % 32
        if cl in A_CL:
            u0[e], u1[e] = x16(x), 1
        elif cl in B_CL:
            u0[e], u1[e] = (x16(x) - x8(x) + 1) % p, x8(x)
        elif cl in C_CL:
            u0[e], u1[e] = (x16(x) - 4 * x8(x) + 4) % p, (2 * x8(x) - 1) % p
        elif cl in SOLO[0]:
            u0[e], u1[e] = pfun[0][e], 0
        elif cl in SOLO[1]:
            u0[e], u1[e] = pfun[1][e], 0
        else:
            u0[e], u1[e] = pfun[2][e], 0
    Scl = [A_CL + B_CL + SOLO[0], A_CL + C_CL + SOLO[1], B_CL + C_CL + SOLO[2]]
    gammas = [g0, g1, g2]
    S = []
    for j in range(3):
        Sj = [e for e in range(n) if e % 32 in Scl[j]]
        assert len(Sj) == 18 * m == 144 >= T_SMALL
        for e in Sj:
            assert pfun[j][e] == (u0[e] + gammas[j] * u1[e]) % p, (j, e)
        S.append(Sj)
    # non-jointness: some row unexplainable on each witness
    for j in range(3):
        e0 = not explainable(u0, S[j], dom, K_SMALL)
        e1 = not explainable(u1, S[j], dom, K_SMALL)
        assert e0 or e1, f"witness {j} jointly explainable"
    # pencil image through base gamma0
    pencils = set()
    for j in (1, 2):
        w1 = [(pfun[j][e] - pfun[0][e]) * inv(gammas[j] - g0) % p
              for e in range(n)]
        w0 = [(pfun[0][e] - g0 * w1[e]) % p for e in range(n)]
        pencils.add((tuple(w0), tuple(w1)))
    assert len(pencils) == 2, "expected exactly two pencils through the base"
    # per-pencil rider bounds
    check_pencil_bounds(u0, u1, {g0: (S[0], pfun[0]), g1: (S[1], pfun[1])},
                        n, T_SMALL, dom, "pencil-A")
    check_pencil_bounds(u0, u1, {g0: (S[0], pfun[0]), g2: (S[2], pfun[2])},
                        n, T_SMALL, dom, "pencil-B")
    print("part 2 verified: BasePencilImageCap boundary (image card = 2) "
          "is attained by a genuine bad family")


def part3_literal_p1():
    NT = N - T
    assert NT == 480946858
    # uniform rider cap
    assert NT + 1 == 480946859
    # consumer: image cap 2 closes the budget
    assert 1 + 2 * NT == 961893717 <= N
    assert 1 + 3 * NT == 1442840575 > N        # 3 pencils no longer close
    # alignment ladder crossover
    m10_floor = T - (N - T) // 9               # 9*(T-A) <= N-T
    assert (N - T) // 9 == 53438539
    assert m10_floor == 539356427
    assert m10_floor ** 2 > N * (K - 1), "10-rider floor must beat Johnson"
    m9_floor = T - (N - T) // 8
    assert m9_floor == 532676609
    assert m9_floor ** 2 <= N * (K - 1), "9-rider floor stays below Johnson"
    # four-witness pigeonhole
    assert 4 * T > 2 * N
    assert 3 * T <= 2 * N                      # three witnesses do not force
    print("part 3 verified: literal P1 constants")
    print(f"  N*(K-1) = {N * (K - 1)}")
    print(f"  10-rider floor {m10_floor}, square {m10_floor**2}")
    print(f"  9-rider floor {m9_floor}, square {m9_floor**2}")


def main():
    part1_one_pencil()
    part2_two_pencils()
    part3_literal_p1()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
