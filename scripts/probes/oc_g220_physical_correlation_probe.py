#!/usr/bin/env python3
# G220 opus-core probe.  NON-OVERLAPPING SEAM: physical-space signed correlation.
#
# Every prior lane worked in MELLIN/character space (G214/G216/G217/G218/G219),
# where the phases of Ŵ(χ)·conj(R̂_r(χ)) equidistribute per every decomposition
# tried (per-rank, inter-rank diff, inter-rank magnitude, shared-factor Ŵ).
#
# But A_r is an EXACT INTEGER: by Parseval,
#     Σ_{χ≠1} Ŵ(χ)·conj(R̂_r(χ)) = p·Σ_x W(x)·R_r(x)  −  (DC term)
# i.e. A_r is (up to normalization + DC) the PHYSICAL-SPACE correlation
#     C_r := Σ_{x∈F_p} W(x)·R_r(x).
# This is a combinatorial count, no phases at all.  The question every Mellin
# probe *avoided*: does C_r have a forced-sign STRUCTURAL decomposition —
# specifically a DIAGONAL / SUPPORT-OVERLAP dominance term that the character-space
# equidistribution scrambles but which survives in physical space?
#
# W(x) = #{(y,z) in G^2 : 2y - z = x}  (the subgroup-translate profile; note the
#   dyadic "2" is the 2-power-subgroup fingerprint).
# R_r(x) = #{(A,B) : A in C(G,r), B in C(G,r-1), sum(A) - sum(B) = x}  (adjacent
#   subset-sum correlation) — wait, R_r as defined is the r-subset-sum COUNT.
# We take R_r(x) = #{A in C(G,r) : sum(A)=x} (Fable's definition) so that
#   R̂_r(χ) = Σ_x R_r(x) χ(x) is the r-th elementary-symmetric character transform.
#
# HYPOTHESES:
#   H_diag  : C_r = Σ_x W(x) R_r(x) is dominated by a DIAGONAL/support-overlap
#             term with a FORCED SIGN (e.g. C_r > mean always, or C_r's deviation
#             from the uniform-null Σ W · Σ R / p has a fixed sign) => a signed
#             lower bound in physical space that Mellin phases hide.  Thinner-than-BGK.
#   H_null  : C_r - (Σ W)(Σ R)/p (the DC-subtracted signed correlation) has NO
#             forced sign / equidistributes in sign across cells => physical space
#             is the SAME wall, no structural dominance.  (matches Mellin no-go.)
#
# We compute EVERYTHING as exact integers (no floats for the sign claim).
import sys
from itertools import combinations


def is_prime(x):
    if x < 2:
        return False
    i = 2
    while i * i <= x:
        if x % i == 0:
            return False
        i += 1
    return True


def order_of(a, p):
    o, cur = 1, a % p
    while cur != 1:
        cur = (cur * a) % p
        o += 1
    return o


def prim_root(p):
    for a in range(2, p):
        if order_of(a, p) == p - 1:
            return a
    raise RuntimeError("no primitive root")


def subgroup(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    pr = prim_root(p)
    h = pow(pr, m, p)
    G, cur = [], 1
    for _ in range(n):
        G.append(cur)
        cur = (cur * h) % p
    return sorted(set(G))


def W_profile(p, G):
    # W(x) = #{(y,z) in G^2 : 2y - z = x}
    W = [0] * p
    for y in G:
        ty = (2 * y) % p
        for z in G:
            W[(ty - z) % p] += 1
    return W


def R_profile(p, G, r):
    # R_r(x) = #{A in C(G,r) : sum(A) = x}
    R = [0] * p
    for A in combinations(G, r):
        R[sum(A) % p] += 1
    return R


def analyze(p, n, r):
    G = subgroup(p, n)
    W = W_profile(p, G)
    R = R_profile(p, G, r)
    sumW = sum(W)          # = n^2
    sumR = sum(R)          # = C(n, r)
    # Raw physical correlation (exact int):
    C = sum(W[x] * R[x] for x in range(p))
    # Uniform-null expectation for the DC term: if W,R were independent uniform,
    # Σ_x W(x) R(x) ~ (Σ W)(Σ R)/p.  The DC-subtracted signed correlation:
    #   A_signed := p * C  -  (Σ W)(Σ R)
    # (this is exactly p·Σ W R - sumW·sumR = the χ≠1 Parseval sum times p,
    #  i.e. proportional to the covariance A_r up to a positive factor.)
    A_signed = p * C - sumW * sumR
    # Also the "diagonal" support-overlap: how much of C comes from x where BOTH
    # W and R are supported (structural), vs the tail.
    overlap_supp = sum(1 for x in range(p) if W[x] > 0 and R[x] > 0)
    return dict(p=p, n=n, r=r, m=(p - 1) // n, sumW=sumW, sumR=sumR,
                C=C, A_signed=A_signed, sign=(1 if A_signed > 0 else (-1 if A_signed < 0 else 0)),
                overlap_supp=overlap_supp, suppR=sum(1 for x in R if x > 0),
                suppW=sum(1 for x in W if x > 0))


def parseval_crosscheck(p, n, r):
    # Verify A_signed = p*C - sumW*sumR equals p * Re Σ_{χ≠1} Ŵ(χ) conj(R̂_r(χ)).
    # Using the exact orthogonality: Σ_x W(x)R(x) uses full χ incl trivial;
    # p*Σ_x W R = Σ_χ Ŵ(χ) conj(R̂(χ))  (Parseval on Z/p, R real so conj ok),
    # and the χ=1 term is (Σ W)(Σ R). So p*C - sumW*sumR = Σ_{χ≠1} Ŵ conj(R̂).
    import cmath
    G = subgroup(p, n)
    W = W_profile(p, G)
    R = R_profile(p, G, r)
    sumW, sumR = sum(W), sum(R)
    C = sum(W[x] * R[x] for x in range(p))
    A_signed = p * C - sumW * sumR
    # character-space sum over all nontrivial additive characters
    acc = 0j
    for k in range(1, p):
        Wh = sum(W[x] * cmath.exp(-2j * cmath.pi * k * x / p) for x in range(p))
        Rh = sum(R[x] * cmath.exp(-2j * cmath.pi * k * x / p) for x in range(p))
        acc += Wh * Rh.conjugate()
    return A_signed, acc.real


def main():
    # Prize-faithful cells: n=2^k, p prime, n|p-1, p>n^3-ish, m=(p-1)/n>1, never n=p-1.
    cells = [
        (8, 41), (8, 73), (8, 97), (8, 257), (8, 60017),
        (16, 97), (16, 257), (16, 881), (16, 977), (16, 1153),
        (32, 193), (32, 257), (32, 641), (32, 1153),
        (64, 641), (64, 769),
    ]
    # Parseval identity cross-check (float, small cell) before the exact sweep:
    a_int, a_char = parseval_crosscheck(97, 8, 5)
    print(f"# PARSEVAL CHECK (p=97,n=8,r=5): A_signed(int)={a_int}  "
          f"char-space Re-sum={a_char:.3f}  rel-err={abs(a_int - a_char)/max(1,abs(a_int)):.2e}",
          flush=True)
    ranks = [5, 6]
    print(f"{'p':>7} {'n':>4} {'m':>6} {'r':>2} {'A_signed':>18} {'sgn':>4} "
          f"{'C':>14} {'ovlp':>6} {'suppR':>6}", flush=True)
    signs = {5: [], 6: []}
    rows = []
    for (n, p) in cells:
        if not is_prime(p):
            print(f"# SKIP p={p} not prime", file=sys.stderr)
            continue
        if (p - 1) % n != 0:
            print(f"# SKIP n={n} not | p-1={p-1}", file=sys.stderr)
            continue
        if n >= r_max_check(n, p):
            pass
        for r in ranks:
            if r > n:
                continue
            if n >= 64 and r >= 6:
                continue  # C(64,6)=74M too slow; r=5 (7.6M) suffices for n=64
            d = analyze(p, n, r)
            rows.append(d)
            signs[r].append((d['p'], d['sign']))
            print(f"{d['p']:>7} {d['n']:>4} {d['m']:>6} {d['r']:>2} "
                  f"{d['A_signed']:>18} {d['sign']:>4} {d['C']:>14} "
                  f"{d['overlap_supp']:>6} {d['suppR']:>6}", flush=True)
    print("\n=== SIGN VERDICT ===")
    for r in ranks:
        s = [x[1] for x in signs[r]]
        pos = sum(1 for v in s if v > 0)
        neg = sum(1 for v in s if v < 0)
        zer = sum(1 for v in s if v == 0)
        print(f"r={r}: {pos} pos, {neg} neg, {zer} zero out of {len(s)} cells "
              f"=> {'FORCED-SIGN candidate' if (pos == 0 or neg == 0) and zer == 0 else 'SIGN NOT FORCED (physical space = same wall)'}")
    # Joint sign realization (the G214 object): are all 4 quadrants of
    # (sign A5, sign A6) realized in physical space too?
    bycell = {}
    for d in rows:
        bycell.setdefault((d['n'], d['p']), {})[d['r']] = d['sign']
    quads = set()
    for k, v in bycell.items():
        if 5 in v and 6 in v:
            quads.add((v[5], v[6]))
    print(f"\nJOINT (sign A5, sign A6) quadrants realized in PHYSICAL space: {sorted(quads)}")
    print(f"  => {'ALL 4 realized => physical space no more structured than Mellin (G214 mirror)' if len(quads) >= 4 else 'NOT all 4 => possible physical-space structural constraint'}")


def r_max_check(n, p):
    return n + 1


if __name__ == '__main__':
    main()
