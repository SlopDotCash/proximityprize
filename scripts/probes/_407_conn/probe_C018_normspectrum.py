"""
C018 norm-spectrum: the TRUE onset of census q-independence is governed by the largest
prime factor (=1 mod n) of any norm N(lambda_S - lambda_T) of a difference of two distinct
r-subset sums of mu_n in Z[zeta_n]. Census_p = I_infty  <=>  p does not divide any such norm
(no mod-p merge). The deficit (census < I_infty) is a MERGE/DEFICIT, not a surplus.

The connection's caveat invokes the resultant threshold (2^mu)^{2^{mu-1}} as the relevant
scale. But the resultant/norm of a single difference of sums of <= n roots of unity has
MODULUS at most (2n)^{phi(n)/?}... actually N(alpha) = prod over conjugates of alpha, each
conjugate has modulus <= 2r <= 2n, and there are phi(2^mu)=2^{mu-1} conjugates, so
|N(alpha)| <= (2n)^{2^{mu-1}}. That is the SAME astronomical scale -- BUT the largest PRIME
FACTOR of N(alpha) is what matters, and that is typically O(log N) ~ O(2^{mu-1} log n) bits,
i.e. the largest prime factor is generically MUCH smaller than N itself.

This probe computes, exactly in Z[zeta_{2^mu}] (reduced mod the 2^mu-th cyclotomic poly,
which is X^{2^{mu-1}} + 1), the set of distinct char-0 subset sums, all pairwise differences,
their integer norms N(alpha) = Res(Phi, alpha) = prod conjugates, factors them, and reports:
  - max |N(alpha)|  vs  (2n)^{2^{mu-1}}  (the resultant-threshold scale)
  - the MAX prime factor p = 1 mod n of any N(alpha)  = the TRUE onset
  - how that onset compares to n^2, n^3, n^4 (prize).

If max-prime-factor (true onset) <= n^{O(1)} with small exponent (~3), the prize p~n^{4-5}
is ABOVE it and census == I_infty in-prize: the connection's "exactness fails in prize" claim
is FALSE for the unconstrained census. The resultant-threshold caveat is vacuously pessimistic.
"""
from math import comb
from itertools import combinations


def feas_set(half, r):
    return [j for j in range(0, r // 2 + 1) if (r - 2 * j) >= 0 and (r - j) <= half]


def I_infty(mu, r):
    half = 2 ** (mu - 1)
    return sum((2 ** (r - 2 * j)) * comb(half, r - 2 * j) for j in feas_set(half, r))


# --- arithmetic in Z[zeta_{2^mu}] = Z[x]/(x^{2^{mu-1}} + 1) ---
def mulmod(a, b, deg):
    """multiply two coeff-vectors (len deg) mod x^deg + 1 (so x^deg = -1)."""
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
                out[k - deg] -= res[k]  # x^deg = -1
    return out


def subset_sum_vec(S, deg, mu):
    """zeta_{2^mu}^k -> x^k reduced mod x^deg+1; sum over k in S."""
    v = [0] * deg
    n_sub = 2 ** mu
    for k in S:
        kk = k % n_sub
        if kk < deg:
            v[kk] += 1
        else:
            v[kk - deg] -= 1  # x^deg = -1
    return v


def norm_of(alpha, deg):
    """N(alpha) for alpha in Z[x]/(x^deg+1) = prod over the deg embeddings = Res(x^deg+1, alpha).
    Compute as the determinant of multiplication-by-alpha matrix (integer)."""
    # build matrix M where column j = alpha * x^j (mod x^deg+1)
    cols = []
    for j in range(deg):
        ej = [0] * deg
        ej[j] = 1
        cols.append(mulmod(alpha, ej, deg))
    # M[i][j] = cols[j][i]
    M = [[cols[j][i] for j in range(deg)] for i in range(deg)]
    return int_det(M)


def int_det(M):
    """Exact integer determinant via fraction-free Bareiss algorithm."""
    from fractions import Fraction
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for i in range(n):
        # pivot
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
            factor = A[k][i] / inv
            for j in range(i, n):
                A[k][j] -= factor * A[i][j]
    return int(det)


def factorize(m):
    m = abs(m)
    if m == 0:
        return {}
    f = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def run(mu, r):
    n = 2 ** mu
    deg = 2 ** (mu - 1)
    Ii = I_infty(mu, r)
    # distinct char-0 subset sums (dedup by coeff vector)
    seen = {}
    for S in combinations(range(n), r):
        v = tuple(subset_sum_vec(S, deg, mu))
        seen[v] = True
    vlist = [list(v) for v in seen.keys()]
    assert len(vlist) == Ii, f"distinct {len(vlist)} != I_infty {Ii}"
    # all pairwise differences -> norms (dedup difference vectors)
    diffs = set()
    for i in range(len(vlist)):
        for j in range(len(vlist)):
            if i == j:
                continue
            d = tuple(vlist[i][t] - vlist[j][t] for t in range(deg))
            diffs.add(d)
    max_norm = 0
    bad_primes = set()  # primes = 1 mod n dividing some norm
    for d in diffs:
        N = norm_of(list(d), deg)
        if abs(N) > max_norm:
            max_norm = abs(N)
        for p in factorize(N):
            if p > 2 and (p - 1) % n == 0:
                bad_primes.add(p)
    onset = max(bad_primes) if bad_primes else None
    thr = n ** deg
    print(f"\nmu={mu} n={n} deg=phi={deg} r={r}: I_infty={Ii}, #distinct-diffs={len(diffs)}")
    print(f"   max |N(lambda_S - lambda_T)| = {max_norm}   resultant-thr (2n)^deg-scale n^deg={thr}")
    print(f"   #primes(=1 mod n) dividing some norm = {len(bad_primes)}")
    if onset:
        import math
        exp = math.log(onset) / math.log(n)
        print(f"   TRUE ONSET (max bad prime =1 mod n) = {onset} = n^{exp:.3f}")
        print(f"      vs n^2={n*n}, n^3={n**3}, n^4(prize)={n**4}, n^5(prize)={n**5}")
        for b in [4, 5]:
            print(f"      prize p~n^{b}={n**b}: {'ABOVE onset (census==I_infty, q-indep)' if n**b>onset else 'BELOW onset'}")
    else:
        print("   no bad primes =1 mod n: census==I_infty for ALL such primes")


def main():
    print("####### C018 norm-spectrum: true onset = max prime(=1 mod n) | N(diff) #######")
    # mu=3 (deg 4) is cheap for all r; mu=4 r=3 (464 distinct -> ~215k diffs, 8x8 dets) ok.
    for r in [3, 4, 5, 6]:
        run(3, r)
    run(4, 3)


if __name__ == "__main__":
    main()
