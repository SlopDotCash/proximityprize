#!/usr/bin/env python3
r"""
probe_largesieve_finalcount_407.py  --  #407: the DEFINITIVE average-over-q count (corrected).

CORRECTED PICTURE (the min-norm-2 alpha are HARMLESS):
  A prime q=1 mod n is BAD at depth r iff q | N(alpha) for some nonzero sparse alpha (deg-1 prime
  divides alpha).  The bad primes are EXACTLY the (correctly-split) prime factors of {N(alpha)}.
  - alpha with N = pure power of 2: NEVER bad for odd q.  (the min-norm wall is irrelevant.)
  - Above max prime factor of all N(alpha) (<= (2r)^{phi}), ALL q are defect-free (norm regime).

THE AVERAGE-OVER-q (large-sieve) MASS BUDGET, rigorous:
  Total bad-incidence mass  =  sum_{alpha != 0} omega_>Q(N(alpha))     (# primes >=Q dividing N(alpha))
  Each alpha: |N(alpha)| <= (2r)^{phi}, so # of its prime factors that are >= Q is
       omega_>=Q(N(alpha)) <= log|N(alpha)| / log Q <= phi*log(2r)/log Q.
  #distinct alpha <= A_r := n^{2r}.   So
       #bad primes in [Q,2Q]  <=  A_r * phi*log(2r)/log Q.
  #available primes (=1 mod n) in [Q,2Q] ~ Q/(phi*log Q).
  GOOD q EXISTS  if  A_r * phi*log(2r)/log Q  <  Q/(phi*log Q),  i.e.
       Q  >  A_r * phi^2 * log(2r)  =  n^{2r} phi^2 log(2r).        (*)

This probe asks the SHARP refined questions the raw (*) hides:
  (1) A_r is NOT n^{2r}: the DISTINCT alpha count is far smaller, AND most have pure-2-power norm
      (harmless). Count the EFFECTIVE A_r = #{alpha : N(alpha) has an odd prime factor >= Q-ish}.
  (2) The mass is concentrated on alpha with SMOOTH norm vs alpha with a LARGE prime factor. A prime
      q ~ Q is hit only by alpha whose norm has q as a factor -- i.e. |N(alpha)| >= Q. How many alpha
      have |N(alpha)| >= Q (only those can hit a prime in [Q,2Q])?  Call it A_r^{>=Q}.
      Then #bad primes <= A_r^{>=Q} * (phi log(2r)/log Q), a MUCH smaller effective count.
  (3) Does refining A_r -> A_r^{>=Q} change the verdict? i.e. is the heavy tail (large-norm alpha)
      rare enough that (*) improves?  We MEASURE the norm distribution exactly and recompute.
"""
import sys, math, itertools
from collections import Counter, defaultdict
import statistics

sys.path.insert(0, 'scripts/probes')

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

def norm_exact(alpha, n):
    h = len(alpha); prim = [t for t in range(1, n, 2)]; prod = 1.0
    for t in prim:
        z = complex(math.cos(2*math.pi*t/n), math.sin(2*math.pi*t/n))
        val = sum(alpha[i]*z**i for i in range(h)); prod *= abs(val)
    return round(prod)

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x


def run(n, r):
    h = n//2
    red = enumerate_reduced(n, r)
    items = list(red.items())
    Er0 = sum(v*v for v in red.values())
    am = defaultdict(int)
    for (rv1, w1) in items:
        for (rv2, w2) in items:
            a = tuple(rv1[j]-rv2[j] for j in range(h))
            if any(a): am[a] += w1*w2
    alphas = list(am.keys())
    norms = [norm_exact(a, n) for a in alphas]
    oddnorms = [odd_part(N) for N in norms]
    A_total = len(alphas)
    A_oddtrivial = sum(1 for o in oddnorms if o == 1)        # pure 2-power norm: harmless
    A_eff = A_total - A_oddtrivial                            # can be bad for some odd q
    print(f"\n{'='*86}\n n={n} r={r}: phi={h}, distinct alpha A_total={A_total}")
    print(f"  A_trivial (N = pure 2-power, NEVER bad for odd q) = {A_oddtrivial}")
    print(f"  A_eff (odd part >1, CAN be bad) = {A_eff}   ({100*A_eff/A_total:.0f}% of alpha)")
    # The largest odd prime factor over all alpha = the defect cap (above it, all q good):
    def largest_prime_factor(x):
        x = odd_part(x); lpf = 1; d = 3
        while d*d <= x:
            while x % d == 0: lpf = d; x //= d
            d += 2
        if x > 1: lpf = max(lpf, x)
        return lpf
    lpfs = [largest_prime_factor(N) for N in norms if odd_part(N) > 1]
    cap = max(lpfs) if lpfs else 1
    print(f"  DEFECT CAP = max odd prime factor of any N(alpha) = {cap} (2^{math.log2(max(cap,1)):.1f}); "
          f"house (2r)^phi=2^{h*math.log2(2*r):.1f}")
    print(f"     => for ALL q>{cap} (q=1 mod n), ZERO defects at depth r={r} (norm regime, PROVEN).")
    # how many alpha have |N| >= a given Q? these are the ONLY ones that can hit a prime ~Q.
    print(f"  alpha norm distribution (|N(alpha)|): "
          f"min={min(norms)}, median={statistics.median(norms)}, max={max(norms)} (2^{math.log2(max(norms)):.1f})")
    for frac in [0.25, 0.5, 0.75, 0.9]:
        thr = max(norms)*frac
        cnt = sum(1 for N in norms if N >= thr)
        print(f"     #alpha with |N| >= {frac:.2f}*max ({thr:.0f}): {cnt} ({100*cnt/A_total:.1f}%)")
    # KEY refined count: a prime q~Q is hit only by alpha with q | N(alpha), so |N(alpha)|>=q>=Q.
    # The number of (alpha, large-prime-factor) incidences where the prime is in the TOP decade:
    # estimate effective covering. We compute, for the largest norms, the actual large prime factors.
    big_factors = Counter()
    for N in norms:
        x = odd_part(N); d = 3
        while d*d <= x:
            while x % d == 0:
                if d > cap**0.5:  # "large" prime factors (the window-scale analog)
                    big_factors[d] += 1
                x //= d
            d += 2
        if x > 1 and x > cap**0.5:
            big_factors[x] += 1
    n_bigprimes = len(big_factors)
    # primes 1 mod n up to cap (the candidate bad window-primes)
    print(f"  large prime factors (> sqrt(cap)={cap**0.5:.0f}) appearing in some N(alpha): {n_bigprimes} distinct")
    print(f"     (these are the primes that DO get hit; each hit by {sum(big_factors.values())/max(n_bigprimes,1):.1f} alpha avg)")
    # the punchline for THIS (n,r): is there a good prime BELOW the cap? almost surely yes since
    # bad primes (factors of norms) are a thin set. Count: # distinct primes 1 mod n in [sqrt(cap),cap]
    # vs # that are bad.
    def is_prime(num):
        if num < 2: return False
        i = 2
        while i*i <= num:
            if num % i == 0: return False
            i += 1
        return True
    lo = int(cap**0.5); hi = cap
    primes_1modn = [q for q in range(lo - lo%n + 1, hi+1, n) if q > 3 and is_prime(q)]
    bad_in_range = set(p for p in big_factors if lo <= p <= hi and p % n == 1)
    print(f"  primes q=1 mod n in [sqrt(cap),cap]=[{lo},{hi}]: {len(primes_1modn)}; "
          f"BAD (divide some N): {len(bad_in_range)} => GOOD fraction "
          f"{1-len(bad_in_range)/max(len(primes_1modn),1):.4f}")


def main():
    print("#"*92)
    print(" #407 DEFINITIVE average-over-q: effective alpha count + defect cap + good-prime density")
    print("#"*92)
    run(8, 3)
    run(8, 4)
    run(8, 5)
    run(16, 2)
    run(16, 3)
    print("\n" + "#"*92)
    print(" SYNTHESIS: bad primes = odd prime factors of {N(alpha)}, capped at (2r)^phi. They are a")
    print(" THIN set (a positive density of primes below the cap are GOOD). The covering criterion (*)")
    print(" Q > n^{2r} phi^2 log(2r) is the FIRST-MOMENT verdict; refined A_eff helps by a constant")
    print(" factor only. At prize depth r~ln q, n^{2r} is astronomical -> (*) vacuous -> first moment")
    print(" CANNOT certify a good q at the floor depth. The covering DOES hold per-depth for r up to the")
    print(" norm-regime r_max ~ 2 log_n q; no average-over-q gain beyond that. Honest: no closure.")


if __name__ == "__main__":
    main()
