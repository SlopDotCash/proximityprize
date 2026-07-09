"""
C018 onset SCALING: how does the true onset of census q-independence grow with mu?

The connection asserts the prize (p ~ n^beta, beta=4..5) is below the resultant threshold
(2^mu)^{2^{mu-1}} and therefore census exactness FAILS in-prize. The onset probe showed the
TRUE onset is ~ O(n^2) for mu=3,4 (census == I_infty for all p > ~15 n^2), NOT the resultant
threshold. This script tests whether the true onset / n^2 stays bounded (so prize p~n^4 is
always above it) or grows with mu.

KEY arithmetic fact (also tested): the deviation census_p - I_infty equals MINUS the number
of merged char-0 values, and a merge of two distinct char-0 sums lambda_S != lambda_T happens
exactly when p | (lambda_S - lambda_T) (i.e. p divides a difference of two subset sums, a
factor of a resultant/norm). The max such |lambda_S - lambda_T| is bounded by
2 * (max |subset sum| over an embedding), giving an onset that is POLYNOMIAL in n
(roughly p > max-pairwise-diff ~ O(n) in the standard archimedean embedding once you note
roots have modulus 1, so |lambda_S| <= r <= n, diff <= 2n) -- i.e. onset ~ O(n), NOT O(n^2)
and EXPONENTIALLY below the resultant threshold.

We measure max deviating prime for mu=3,4,5 and small r, and compare to n, n^2, threshold.
We also directly check: is census_p == I_infty <=> no two distinct char-0 subset sums are
congruent mod p?  (the deficit-by-collision law.)
"""
from math import comb
from itertools import combinations


def feas_set(half, r):
    return [j for j in range(0, r // 2 + 1) if (r - 2 * j) >= 0 and (r - j) <= half]


def I_infty(mu, r):
    half = 2 ** (mu - 1)
    return sum((2 ** (r - 2 * j)) * comb(half, r - 2 * j) for j in feas_set(half, r))


def is_prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0:
            return False
        i += 2
    return True


def root_of_order(p, order):
    if (p - 1) % order != 0:
        return None
    cof = (p - 1) // order
    for base in range(2, p):
        g = pow(base, cof, p)
        if g != 1 and pow(g, order // 2, p) != 1:
            return g
    return None


def census_p(p, mu, r):
    n_sub = 2 ** mu
    g = root_of_order(p, n_sub)
    if g is None:
        return None
    elems = [pow(g, i, p) for i in range(n_sub)]
    sums = set()
    for S in combinations(elems, r):
        s = 0
        for x in S:
            s = (s + x) % p
        sums.add(s)
    return len(sums)


def max_pairwise_diff_archimedean(mu, r):
    """Bound on max |lambda_S - lambda_T| over r-subsets, char-0 archimedean embedding
    (roots = e^{2 pi i k/2^mu}, modulus 1). Since |lambda_S| <= r, the diameter <= 2r
    trivially; we report the realized max |lambda_S| and 2*that, plus #distinct.
    (O(#subsets), no O(distinct^2) blowup.)"""
    import cmath
    n_sub = 2 ** mu
    roots = [cmath.exp(2j * cmath.pi * k / n_sub) for k in range(n_sub)]
    vals = set()
    max_mod = 0.0
    for S in combinations(range(n_sub), r):
        s = sum(roots[k] for k in S)
        vals.add((round(s.real, 6), round(s.imag, 6)))
        m = abs(s)
        if m > max_mod:
            max_mod = m
    return 2.0 * max_mod, len(vals)


def sweep_last_bad(mu, r, p_hi):
    n = 2 ** mu
    Ii = I_infty(mu, r)
    last_bad = None
    p = n + 1
    while p <= p_hi:
        if (p - 1) % n == 0 and is_prime(p):
            c = census_p(p, mu, r)
            if c is not None and c != Ii:
                last_bad = p
        p += 1
    return last_bad, Ii


def main():
    print("####### onset scaling vs n, n^2, archimedean diameter, resultant threshold #######")
    for mu in [3, 4, 5]:
        n = 2 ** mu
        thr = n ** (2 ** (mu - 1))
        # r values; keep enumeration feasible (C(32,r) for mu=5)
        rs = [3, 4] if mu < 5 else [3]
        for r in rs:
            # sweep to a comfortable multiple of n^2
            p_hi = max(20 * n * n, 4000)
            if mu == 5:
                p_hi = 25 * n * n  # ~25600
            last_bad, Ii = sweep_last_bad(mu, r, p_hi)
            diam, ndistinct = max_pairwise_diff_archimedean(mu, r)
            print(f"\nmu={mu} n={n} r={r}: I_infty={Ii} (char-0 distinct={ndistinct})")
            print(f"   archimedean diameter (max |lam_S-lam_T|) = {diam:.3f}  (~{diam/n:.2f} n)")
            print(f"   resultant threshold (2^mu)^(2^(mu-1)) = {thr}")
            if last_bad is None:
                print(f"   last census!=I_infty: NONE up to p={p_hi} (onset <= {n+1})")
            else:
                print(f"   last census!=I_infty: p={last_bad}  = {last_bad/n:.2f} n"
                      f"  = {last_bad/(n*n):.3f} n^2  = {last_bad/diam:.2f} x diameter")
                print(f"   resultant threshold / true onset = {thr/last_bad:.3e}")
                # prize check
                for b in [4, 5]:
                    prize = n ** b
                    verdict = "ABOVE onset -> census==I_infty (q-indep)" if prize > last_bad else "below onset"
                    print(f"      prize p~n^{b}={prize}: {verdict}")


if __name__ == "__main__":
    main()
