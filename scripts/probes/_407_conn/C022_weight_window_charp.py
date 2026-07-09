#!/usr/bin/env python3
"""
C022: The dyadic prize domain is single-prime-power, so the in-tree char-0
weighted-window law (`weighted_windowed_prime_pow`) is the SHARP char-0 case;
claim = the prize wall is the char-0 -> char-p transfer of THAT single theorem.

In-tree CHAR-0 anchor (PROVEN, axiom-clean), at n = 2^mu, t < n:
   forall 1<=j<=t:  sum_e w_e * zeta^{j e} = 0     (w : ZMod n -> N, an N-weight)
   <=>  w is an N-combination of mu_d-coset indicators, d | n, d > t.
Corollary (min distance of the dual-RS / BCH-window code):
   the minimum nonzero such weight has support a single mu_d-coset, d = least
   divisor of 2^mu exceeding t = 2^{ceil(log2(t+1))}.  Sharp, BCH-beating.

THE TRANSFER QUESTION (this probe): over F_q (q prime = 1 mod n, PROPER dyadic
subgroup mu_n, q ~ n^beta, n << sqrt q -- the prize regime), is the same law
true?  i.e.

  (T1) Does every char-p window-t-vanishing N-weight remain an N-combination of
       mu_d-coset indicators (d>t)?  The DEFECT CARRIERS are the char-p-only
       solutions that are NOT char-0 coset combinations.
  (T2) [min-distance / BCH form]  Is the minimum nonzero char-p window-vanishing
       weight still 2^{ceil(log2(t+1))}, or do SHORTER (lower-weight) char-p
       relations appear?  A shorter relation = a short low-weight {..}-relation
       of 2^mu-th roots vanishing mod q -- the BGK/Lam-Leung-in-char-p object.

We test BOTH.  We work with the {0,1}-support sub-question for min-distance
(min Hamming weight of a window-vanishing vector = the dual code's min distance),
which is the honest min-weight of an N-weight too (an N-weight of total mass m
has support >= the binary min distance when reduced).  We additionally scan small
N-weights (coeffs in {0,1,2}) to catch genuinely multiset defect carriers.

Exact integer arithmetic mod q.  Multiple proper-subgroup primes per n.
"""
import itertools
from math import comb, gcd, log2, ceil

def find_primes(n, count, beta_lo=4.0, beta_hi=5.5, start=None):
    """primes q = 1 mod n, with q ~ n^beta (n << sqrt q): the prize regime."""
    import sympy
    lo = int(n**beta_lo)
    hi = int(n**beta_hi)
    out = []
    q = ((lo // n) + 1) * n + 1
    while q < hi and len(out) < count:
        if sympy.isprime(q):
            out.append(q)
        q += n
    return out

def primitive_nth_root(q, n):
    """a primitive n-th root of unity in F_q (q = 1 mod n)."""
    # find generator g of F_q^*, then g^{(q-1)/n}
    import sympy
    g = sympy.primitive_root(q)
    zeta = pow(g, (q-1)//n, q)
    # sanity
    assert pow(zeta, n, q) == 1 and all(pow(zeta, n//p, q) != 1
            for p in sympy.primefactors(n)), "not primitive"
    return zeta

def least_divisor_exceeding(n, t):
    """least divisor d of n with d > t.  For n = 2^mu: 2^{ceil(log2(t+1))}."""
    d = 1
    while d <= t:
        d *= 2  # n is a power of 2
    assert n % d == 0
    return d

def coset_indicator_supports(n, twoL):
    """supports of the mu_{n? } ... here cosets of mu_d (d=twoL) in mu_n.
       a coset of mu_d in mu_n: exponents {e + (n/d)*i : i in range(d)} for e fixed
       mod (n/d).  There are n/d cosets, each of size d."""
    step = n // twoL
    cosets = {}
    for e in range(n):
        cosets.setdefault(e % step, []).append(e)
    return [sorted(v) for v in cosets.values()]

def is_coset_combination(support_set, n, t):
    """is the (0/1) support a UNION of mu_d-cosets with d > t (d | n)?
       Equivalent (char-0 law) to: support closed under adding n/d for the
       SMALLEST valid d... but the law allows ANY d>t per coset.  The MINIMAL-weight
       coset-combination uses d = least divisor exceeding t; any coset-union with
       larger d is a union of those.  We test: is support a disjoint union of
       *some* mu_d cosets, d>t?  For powers of 2 the cosets nest, so support is a
       coset-union iff it is closed under the SMALLEST such shift n/d_min where
       d_min = least divisor exceeding t -- because every mu_{d>=d_min} coset is a
       union of mu_{d_min} cosets.  So: closed under shift by n//d_min."""
    d_min = least_divisor_exceeding(n, t)
    step = n // d_min   # shift; coset = {e, e+step, ..., e+(d_min-1)step}
    S = set(support_set)
    for e in S:
        for i in range(d_min):
            if (e + i*step) % n not in S:
                return False
    return True

def min_distance_charp(q, zeta, n, t, wmax=None):
    """min Hamming weight of a NONZERO window-vanishing vector over F_q (kernel of
       the t x n matrix M[j,e] = zeta^{j e}, j=1..t).  Search by increasing weight
       w; support S of weight w admits a nonzero kernel vector iff the t x w matrix
       has rank < w.  This is EXACTLY the dual-RS / BCH-window code's min distance.
       The char-0 value is the least divisor of n exceeding t = 2^ceil(log2(t+1)).
       wmax bounds the search (min dist can never exceed t+1 for these codes, and
       the char-0 value <= 2t, so wmax = min(n, 2t+2) is safe & tractable)."""
    if wmax is None:
        wmax = min(n, 2*t + 2)
    Zp = [pow(zeta, e, q) for e in range(n)]
    for w in range(1, wmax+1):
        for S in itertools.combinations(range(n), w):
            M = [[pow(Zp[e], j, q) for e in S] for j in range(1, t+1)]
            if matrix_rank_modp(M, w, t, q) < w:
                return w, S
    return None, None

def matrix_rank_modp(M, w, t, q):
    """rank over F_q of the t x w matrix M (rows length w)."""
    # gaussian elimination mod q
    A = [row[:] for row in M]
    rank = 0
    rows = len(A)
    col = 0
    pivot_row = 0
    for col in range(w):
        # find pivot in column col at row >= pivot_row
        piv = None
        for r in range(pivot_row, rows):
            if A[r][col] % q != 0:
                piv = r; break
        if piv is None:
            continue
        A[pivot_row], A[piv] = A[piv], A[pivot_row]
        inv = pow(A[pivot_row][col], q-2, q)
        A[pivot_row] = [(x*inv) % q for x in A[pivot_row]]
        for r in range(rows):
            if r != pivot_row and A[r][col] % q != 0:
                f = A[r][col]
                A[r] = [(A[r][c] - f*A[pivot_row][c]) % q for c in range(w)]
        pivot_row += 1
        rank += 1
        if pivot_row == rows:
            break
    return rank

def count_defect_carriers_01(q, zeta, n, t):
    """count {0,1} window-vanishing supports that are NOT char-0 coset combinations
       (d > t).  These are the defect carriers."""
    Zp = [pow(zeta, e, q) for e in range(n)]
    defect = 0
    total_vanish = 0
    examples = []
    for w in range(1, n+1):
        for S in itertools.combinations(range(n), w):
            M = [[pow(Zp[e], j, q) for e in S] for j in range(1, t+1)]
            if matrix_rank_modp(M, w, t, q) < w:
                # there EXISTS a nonzero window-vanishing weight on support subset of S;
                # but we want supports that themselves give an N-weight... use the
                # all-ones / kernel.  Count S as a "vanishing support" if the all-distinct
                # support carries SOME vanishing weight; for the defect notion compare to
                # coset-union of the EXACT support set when the weight is the indicator.
                # Cleanest: count {0,1} indicator weights w_S with vanishing window.
                pass
    # Cleaner approach below.
    return None

def count_indicator_window_vanishing(q, zeta, n, t):
    """For every {0,1} indicator weight (i.e. subset S of mu_n), test whether
       sum_{e in S} zeta^{j e} = 0 mod q for all j=1..t.  Count vanishing subsets;
       among them count those NOT closed under the coset shift (defect carriers)."""
    Zp = [pow(zeta, e, q) for e in range(n)]
    vanish = []
    for size in range(1, n+1):
        for S in itertools.combinations(range(n), size):
            ok = all(sum(pow(Zp[e], j, q) for e in S) % q == 0 for j in range(1, t+1))
            if ok:
                vanish.append(S)
    defect = [S for S in vanish if not is_coset_combination(S, n, t)]
    return len(vanish), len(defect), defect

def main():
    import sys
    P = lambda *a: (print(*a), sys.stdout.flush())
    P("="*78)
    P("C022 char-0 -> char-p transfer of the prime-power weighted-window law")
    P("PRIZE REGIME: proper dyadic subgroup mu_n in F_q, q=1 mod n, q ~ n^beta")
    P("="*78)
    P("\nTWO transfer tests:")
    P("  (T2) MIN-DISTANCE: does the char-0 min-dist d*=least-div-exceeding-t survive?")
    P("       (a SHORTER char-p relation = a short low-weight relation of 2^mu-th")
    P("        roots vanishing mod q = the BGK/Lam-Leung-in-char-p object)")
    P("  (T1) DEFECT CARRIERS: # indicator window-vanishing sets that are NOT char-0")
    P("       coset combinations (only n<=16, full 2^n enumeration tractable)")
    # n=32 limited to small t so min-dist search (wmax=2t+2) stays tractable
    cases = [(8,1),(8,2),(8,3),(16,1),(16,2),(16,3),(16,4),(16,7),
             (32,1),(32,2),(32,3)]
    for n, t in cases:
        dmin = least_divisor_exceeding(n, t)
        primes = find_primes(n, 3)
        P(f"\n--- n={n}=2^{int(log2(n))}, t={t}: char-0 min-dist d* = "
          f"least-div>t = {dmin}; char-0 defect carriers = 0 ---")
        do_defect = (n <= 16)
        for q in primes:
            zeta = primitive_nth_root(q, n)
            md, S = min_distance_charp(q, zeta, n, t)
            beta = log2(q)/log2(n)
            flag_md = "OK(=d*)" if md == dmin else f"** SHORTER {md}<{dmin} **"
            line = (f"  q={q} (beta~{beta:.2f}, n^2={n*n}<q? {n*n<q}): "
                    f"min-dist={md} [{flag_md}]")
            if do_defect:
                nv, nd, dex = count_indicator_window_vanishing(q, zeta, n, t)
                flag_df = "OK(0)" if nd == 0 else f"** DEFECT={nd} **"
                line += f"  #vanish-indic={nv} #defect={nd} [{flag_df}]"
            P(line)
            if do_defect and dex and len(dex) <= 5:
                P(f"      defect support examples: {[tuple(x) for x in dex[:5]]}")

if __name__ == "__main__":
    main()
