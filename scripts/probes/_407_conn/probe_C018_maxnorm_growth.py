"""
C018 max-norm growth: is max |N(lambda_S - lambda_T)| polynomial in n, or does it grow like
the resultant-threshold (2n)^{phi(n)} (super-polynomial)? The onset of census q-independence
is <= max prime factor <= max_norm, so the SCALE of max_norm decides whether the prize
(p~n^{4-5}) is above the onset for ALL mu (closing the q-independence claim in-prize) or
whether large mu eventually pushes the onset above the prize (the honest W-LamLeung wall).

We compute max |N(diff)| for mu=3,4,5,6 at r=2 (cheapest, fewest distinct sums, but exposes
the largest single differences -- antipodal-free pairs sum to roots far apart) and r=3, and
fit the exponent log(max_norm)/log(n).

For r=2: distinct sums are {zeta^a + zeta^b}; differences are sums/diffs of <=4 roots of unity;
norms are small and exactly computable even at mu=6 (deg 32) because #distinct is O(n^2).
"""
from math import comb, log
from itertools import combinations
from fractions import Fraction


def mulmod(a, b, deg):
    res = [0] * (2 * deg - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj:
                res[i + j] += ai * bj
    out = [0] * deg
    for k in range(2 * deg - 1):
        if res[k]:
            if k < deg:
                out[k] += res[k]
            else:
                out[k - deg] -= res[k]
    return out


def subset_sum_vec(S, deg, mu):
    v = [0] * deg
    n_sub = 2 ** mu
    for k in S:
        kk = k % n_sub
        if kk < deg:
            v[kk] += 1
        else:
            v[kk - deg] -= 1
    return v


def int_det(M):
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for i in range(n):
        if A[i][i] == 0:
            sw = None
            for k in range(i + 1, n):
                if A[k][i] != 0:
                    sw = k
                    break
            if sw is None:
                return 0
            A[i], A[sw] = A[sw], A[i]
            det = -det
        det *= A[i][i]
        inv = A[i][i]
        for k in range(i + 1, n):
            f = A[k][i] / inv
            for j in range(i, n):
                A[k][j] -= f * A[i][j]
    return int(det)


def norm_of(alpha, deg):
    cols = []
    for j in range(deg):
        ej = [0] * deg
        ej[j] = 1
        cols.append(mulmod(alpha, ej, deg))
    M = [[cols[j][i] for j in range(deg)] for i in range(deg)]
    return int_det(M)


def max_norm(mu, r):
    n = 2 ** mu
    deg = 2 ** (mu - 1)
    seen = {}
    for S in combinations(range(n), r):
        seen[tuple(subset_sum_vec(S, deg, mu))] = True
    vlist = [list(v) for v in seen.keys()]
    mx = 0
    # only need pairwise diffs; dedup
    diffs = set()
    for i in range(len(vlist)):
        for j in range(i + 1, len(vlist)):
            d = tuple(vlist[i][t] - vlist[j][t] for t in range(deg))
            diffs.add(d)
    for d in diffs:
        N = abs(norm_of(list(d), deg))
        if N > mx:
            mx = N
    return mx, len(vlist), len(diffs)


def main():
    print("####### C018 max-norm growth vs resultant threshold (2n)^phi #######")
    print("If max_norm ~ n^c (polynomial, c small), onset <= max_norm stays poly => prize above it.")
    print("If max_norm ~ (2n)^{phi=n/2} (super-poly), the resultant caveat bites at large mu.\n")
    import sys
    for r in [2, 3]:
        print(f"--- r={r} ---")
        sys.stdout.flush()
        prev = None
        for mu in [3, 4, 5]:
            n = 2 ** mu
            deg = 2 ** (mu - 1)
            # r=3 at mu=5 (deg 16, distinct ~4512 -> ~10M diffs of 16x16 dets) too heavy; skip
            if r == 3 and mu == 5:
                print(f"  mu={mu} n={n}: (skipped r=3 at mu=5 -- too heavy)")
                sys.stdout.flush()
                continue
            mx, ndist, ndiff = max_norm(mu, r)
            thr = (2 * n) ** deg
            exp = log(mx) / log(n) if mx > 1 else 0.0
            growth = f"  (x{mx/prev:.1f} vs prev)" if prev else ""
            print(f"  mu={mu} n={n} deg={deg}: max_norm={mx} = n^{exp:.3f}{growth}"
                  f"   resultant-thr (2n)^deg={thr}   ratio thr/maxnorm={thr/mx:.2e}")
            sys.stdout.flush()
            prev = mx
        print()


if __name__ == "__main__":
    main()
