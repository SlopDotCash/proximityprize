#!/usr/bin/env python3
r"""
probe_largesieve_cover_407.py  --  #407: THE COVERING QUESTION (does the bad set cover [Q,2Q]?).

The deep probe showed: a GOOD q (D<=baseline) exists in 78-86% of the window even where defects are
common, and the first moment E_q[D] is dominated by a FEW low-norm alpha (alpha=(3,0,0,-1), L2^2=10)
that carry HUGE multiplicity. The honest large-sieve question is NOT "is E_q[D] small" (it isn't --
heavy tail) but:

   Does the union of bad-prime-sets  B = union_{alpha != 0} {q in [Q,2Q] : q | alpha}  COVER [Q,2Q]?
   If B != [Q,2Q], a GOOD q (D=0, no defect) EXISTS and the explicit-code prize is satisfiable.

For a FIXED alpha != 0 in Z[zeta_n] (sparse, <=2r roots), the bad primes are EXACTLY the q with a
degree-1 prime above q dividing alpha, a SUBSET of {q : q | N(alpha)}.  So
   #{bad q for alpha} <= omega(N(alpha)) <= log|N(alpha)|/log 2 <= (phi/2)*log2(L2^2(alpha))   (tiny).
The DANGER is the SMALL-NORM alpha: |N(alpha)| can be as small as... the smallest possible norm of a
nonzero sparse cyclotomic integer. THE COVERING FAILS TO BE A PROBLEM iff the number of DISTINCT bad
primes (counted once each, NOT weighted by mult) is < #primes in window.

THIS PROBE measures, over a LARGE window of primes (so we see asymptotics in #Q):
   (1) #distinct bad primes  vs  #primes in window  (the covering ratio);
   (2) for each alpha, omega = #distinct primes it kills, summed = an UPPER bound on #bad primes
       (union bound);  the TRUE #bad primes (union) is smaller (overlaps);
   (3) the smallest-norm alpha and HOW MANY primes each kills as the window grows
       (does a fixed small-norm alpha kill a POSITIVE FRACTION of primes? -- the real obstruction);
   (4) the asymptotic fraction of good primes as Q grows (fixed r): does it -> 1, a constant, or 0?

If the good-prime fraction stays bounded below by c>0 as Q->infty (fixed n,r), then for ALMOST ALL q
the floor holds AT THAT DEPTH, and an explicit good q exists -- a genuine partial result for the
explicit-code prize (at fixed depth r; the prize needs r~ln q, the deep limit).
"""
import sys, math, itertools
from collections import Counter, defaultdict
import statistics

sys.path.insert(0, 'scripts/probes')

def is_prime(num):
    if num < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if num % q == 0: return num == q
    d = num-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, num)
        if x in (1, num-1): continue
        for _ in range(s-1):
            x = x*x % num
            if x == num-1: break
        else: return False
    return True

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x

def primitive_root(p):
    phi = p-1; facs = []; mm = phi; d = 2
    while d*d <= mm:
        if mm % d == 0:
            facs.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: facs.append(mm)
    for g in range(2, p):
        if all(pow(g, phi//qq, p) != 1 for qq in facs): return g

def order_n_root(p, n):
    g = primitive_root(p)
    return pow(g, (p-1)//n, p)

def reduced_vec(coeff, n):
    h = n//2
    return tuple(coeff[j] - coeff[j+h] for j in range(h))

def enumerate_reduced(n, r):
    red = defaultdict(int)
    for tup in itertools.combinations_with_replacement(range(n), r):
        coeff = [0]*n
        for t in tup: coeff[t] += 1
        cc = Counter(tup)
        num = math.factorial(r); den = 1
        for v in cc.values(): den *= math.factorial(v)
        red[reduced_vec(coeff, n)] += num//den
    return red

def alpha_zero_mod_q(alpha, zpows, q):
    val = 0
    for j, a in enumerate(alpha):
        if a: val += a*zpows[j]
    return val % q == 0


def run(n, r, Qlo, Qhi, label):
    h = n//2
    red = enumerate_reduced(n, r)
    red_items = list(red.items())
    Er0 = sum(v*v for v in red.values())
    offdiag = n**(2*r) - Er0
    alpha_mult = defaultdict(int)
    for (rv1, w1) in red_items:
        for (rv2, w2) in red_items:
            alpha = tuple(rv1[j]-rv2[j] for j in range(h))
            if any(alpha): alpha_mult[alpha] += w1*w2
    alphas = list(alpha_mult.keys())
    # sort by norm (L2^2) ascending so we track the dangerous small ones
    alphas.sort(key=lambda a: sum(x*x for x in a))

    # primes in [Qlo, Qhi], q=1 mod n, deep-sparse
    qs = []
    q = Qlo - (Qlo % n) + 1
    if q < Qlo: q += n
    while q <= Qhi:
        if q > 3 and is_prime(q) and odd_part((q-1)//n) > 1:
            qs.append(q)
        q += n
    nq = len(qs)
    print(f"\n{'='*88}\n {label}: n={n} r={r}  window [{Qlo},{Qhi}] = {nq} primes "
          f"(2^{math.log2(qs[0]):.1f}..2^{math.log2(qs[-1]):.1f})\n{'='*88}")
    print(f"  E_r^0={Er0}, offdiag={offdiag}, #distinct alpha={len(alphas)}")

    bad_primes = set()         # union of all bad q (D>0)
    bad_above_baseline = set() # q with D > baseline
    alpha_kills = defaultdict(list)  # alpha -> list of primes it kills
    D_per_q = {}
    baseline_at = lambda q: offdiag / q
    for q in qs:
        z = order_n_root(q, n)
        zpows = [pow(z, j, q) for j in range(h)]
        D = 0
        for a in alphas:
            if alpha_zero_mod_q(a, zpows, q):
                D += alpha_mult[a]
                alpha_kills[a].append(q)
                bad_primes.add(q)
        D_per_q[q] = D
        if D > baseline_at(q):
            bad_above_baseline.add(q)

    n_zero = nq - len(bad_primes)
    n_good = nq - len(bad_above_baseline)
    print(f"  COVERING:  #distinct bad primes (D>0) = {len(bad_primes)}/{nq}  "
          f"=> #q with D==0 (no defect) = {n_zero} ({100*n_zero/nq:.1f}%)")
    print(f"             #q above baseline (D>offdiag/q) = {len(bad_above_baseline)}/{nq}  "
          f"=> #GOOD q = {n_good} ({100*n_good/nq:.1f}%)")
    # union bound vs truth
    union_bound = sum(len(set(alpha_kills[a])) for a in alphas)
    print(f"  union bound sum_alpha omega = {union_bound}  (>= true #bad primes {len(bad_primes)}; "
          f"overlap factor {union_bound/max(len(bad_primes),1):.2f})")
    # the dangerous small-norm alpha: how many primes does each kill, and what FRACTION
    print(f"  small-norm alpha (the heavy tail) -- #primes each kills out of {nq}:")
    shown = 0
    for a in alphas:
        k = len(set(alpha_kills[a]))
        if k == 0: continue
        l2 = sum(x*x for x in a)
        print(f"     alpha={a} L2^2={l2} mult={alpha_mult[a]}: kills {k} primes "
              f"(frac {k/nq:.4f}); omega-bound {(h//1)*math.log2(max(l2,2)):.1f}")
        shown += 1
        if shown >= 8: break
    print(f"  ==> GOOD q EXISTS in window: {n_good>0}  (fraction good {n_good/nq:.4f}). "
          f"defect-free q exists: {n_zero>0} (frac {n_zero/nq:.4f}).")
    return n_zero/nq, n_good/nq, nq


def main():
    print("#"*92)
    print(" #407 LARGE-SIEVE COVERING: does the bad set cover the prime window? (good explicit q?)")
    print("#"*92)
    # Track the good-fraction as the window grows at FIXED (n,r). n=16,r=2: threshold 256, so
    # defects appear for q<256 and vanish above -> good fraction -> 1. We want to see the trend.
    print("\n--- n=16, r=2: norm threshold (2r)^4 = 256.  Watch good-fraction grow with Q ---")
    for (lo, hi) in [(16, 256), (256, 1024), (1024, 4096), (4096, 16384)]:
        run(16, 2, lo, hi, f"band[{lo},{hi}]")
    print("\n--- n=8, r=4: norm threshold (2r)^4=4096.  Defect-rich; watch covering ---")
    for (lo, hi) in [(8, 256), (256, 2048), (2048, 16384)]:
        run(8, 4, lo, hi, f"band[{lo},{hi}]")


if __name__ == "__main__":
    main()
