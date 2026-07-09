#!/usr/bin/env python3
r"""
probe_largesieve_secondmoment_407.py  --  #407: can the SECOND moment beat the first-moment union bound?

FINDING SO FAR (first moment, probe_largesieve_prizescale): the union bound #B <= n^{2r} phi log(2r)/log Q
reproduces the norm-regime depth r~3 at prize scale -- NO improvement over the char-0 transfer wall.
The bound is driven by the SHEER NUMBER of alpha (n^{2r}), each contributing a few bad primes.

THE SECOND-MOMENT HOPE: the first moment overcounts because many alpha share the same prime divisor
(a prime q is bad iff ANY alpha vanishes; the union is smaller than the sum). If the bad primes
CLUSTER (the small-norm dangerous alpha all divide a few common primes), the true bad SET is tiny and
a good q exists with room to spare. The 2nd moment over q,
     M2 = (1/#Q) sum_q D(q)^2 = sum_{alpha,alpha'} mult*mult' * P_q(q | alpha AND q | alpha'),
detects this: cross terms q|alpha & q|alpha' are nonzero only when alpha,alpha' share a prime, i.e.
when gcd-structure links them. Large M2/M1^2 (overdispersion) = clustering = good (bad q concentrated).

BUT THE REAL TEST for the COVERING claim is different: we want the SIZE OF THE UNION of bad primes,
not D(q). The relevant second-moment / large-sieve inequality is the DUAL:
     sum_{q in window} | sum_alpha a_alpha [q | alpha] |^2   <=  (large-sieve)  ...
This probe measures, over a real window where defects exist:
  (1) M1 (#distinct bad primes / #Q)  and the union-bound estimate sum_alpha omega(N(alpha))/#Q;
  (2) the OVERLAP: do small-norm alpha share prime divisors? (cluster -> union much < sum);
  (3) whether #distinct-bad-primes / #Q  -> 0 as Q grows at FIXED r below norm threshold (the only
      hope: even though union BOUND is vacuous at r~ln q, the TRUE bad fraction might ->0);
  (4) the structural reason: the smallest |N(alpha)| over nonzero sparse alpha = the HOUSE/norm wall.
      A small-norm alpha (e.g. N=2 if it existed) would divide ~1/2 of all primes => bad fraction ~const>0
      => NO good q asymptotically. So the covering hope LIVES OR DIES on: is min |N(alpha)| large?
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
    return pow(primitive_root(p), (p-1)//n, p)

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
    """|N_{Q(zeta_n)/Q}(alpha)| for alpha in reduced power-basis coords (len phi(n)), n=2^a.
       Product over primitive n-th roots zeta^t, t odd in [1,n)."""
    h = len(alpha)
    prim = [t for t in range(1, n, 2)]   # t coprime to n=2^a iff t odd; phi=n/2 of them
    prod = 1.0
    for t in prim:
        z = complex(math.cos(2*math.pi*t/n), math.sin(2*math.pi*t/n))
        val = sum(alpha[i]*z**i for i in range(h))
        prod *= abs(val)
    return prod


def run(n, r):
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
    # exact norms
    norms = {}
    for a in alphas:
        N = norm_exact(a, n)
        norms[a] = round(N)
    minnorm = min(norms.values())
    nrm_sorted = sorted(norms.values())
    print(f"\n{'='*86}\n n={n} r={r}: phi={h}, #alpha={len(alphas)}, offdiag={offdiag}")
    print(f"  EXACT |N(alpha)| over nonzero sparse alpha:")
    print(f"     MIN |N| = {minnorm}  (2^{math.log2(max(minnorm,1)):.2f})   "
          f"house bound (2r)^phi = {(2*r)**h} (2^{h*math.log2(2*r):.1f})")
    print(f"     |N| distribution: min={nrm_sorted[0]}, 10%={nrm_sorted[len(nrm_sorted)//10]}, "
          f"median={statistics.median(nrm_sorted)}, max={nrm_sorted[-1]}")
    # how many alpha attain the MIN norm? (the most dangerous)
    n_minnorm = sum(1 for v in norms.values() if v == minnorm)
    print(f"     #alpha attaining min-norm {minnorm}: {n_minnorm}")
    # density argument: a fixed alpha with norm N divides a prime q (=1 mod n, deg-1) with 'probability'
    # ~ (number of prime ideals of norm-related divisibility). For the SINGLE embedding, q | alpha(g)
    # happens for q | the integer alpha(g_q); but g_q varies. The right density: among primes q=1 mod n,
    # the fraction with q | alpha = the deg-1 prime above q divides alpha = #{q | N(alpha), split right}.
    # Over a window of T primes, expected #bad for this alpha ~ omega(N(alpha)) <= log N / log Q.
    # The KEY: min-norm alpha has the SMALLEST norm => contributes <= log(minnorm)/log Q bad primes,
    # which is O(1) NOT a positive fraction. So even the worst alpha kills only O(1) primes per window.
    print(f"  => worst (min-norm) alpha kills <= log2(N)/log2(Q) = {math.log2(max(minnorm,2)):.1f}/log2(Q) primes.")
    print(f"     This is O(1/log Q) FRACTION per alpha; the union over {len(alphas)} alpha is the question.")

    # Now MEASURE the true bad-prime fraction over a growing window (fixed r), to see asymptotics.
    print(f"  measuring true bad-prime fraction over growing windows (fixed r={r}):")
    for (Qlo, Qhi) in [(minnorm//2, minnorm*2), (minnorm*2, minnorm*8), (minnorm*8, minnorm*32),
                       (minnorm*32, minnorm*128)]:
        Qlo = max(Qlo, 2*n)
        qs = []
        q = Qlo - (Qlo % n) + 1
        if q < Qlo: q += n
        while q <= Qhi and len(qs) < 2000:
            if q > 3 and is_prime(q) and odd_part((q-1)//n) > 1: qs.append(q)
            q += n
        if not qs: continue
        bad = set(); badbase = 0
        for q in qs:
            z = order_n_root(q, n); zpows = [pow(z, j, q) for j in range(h)]
            D = 0
            for a in alphas:
                val = 0
                for j in range(h):
                    if a[j]: val += a[j]*zpows[j]
                if val % q == 0:
                    D += alpha_mult[a]; bad.add(q)
            if D > offdiag/q: badbase += 1
        fr_defectfree = 1 - len(bad)/len(qs)
        fr_good = 1 - badbase/len(qs)
        print(f"     Q in [{qs[0]},{qs[-1]}] (2^{math.log2(qs[0]):.1f}..2^{math.log2(qs[-1]):.1f}), {len(qs)} primes: "
              f"defect-free frac={fr_defectfree:.4f}, good(<=baseline) frac={fr_good:.4f}")


def main():
    print("#"*90)
    print(" #407 SECOND-MOMENT / min-norm: does the bad-prime fraction -> 0? (the covering hope)")
    print("#"*90)
    run(8, 3)
    run(8, 4)
    run(16, 2)
    run(16, 3)
    print("\nKEY: if min|N(alpha)| GROWS with the depth/scale, the worst alpha still kills only O(log N)")
    print("primes and the defect-free fraction -> 1 as Q grows (FIXED r). The covering holds per-depth.")
    print("The PRIZE obstruction is that the floor needs ALL r up to ~ln q SIMULTANEOUSLY at ONE fixed q,")
    print("and #alpha = n^{2r} grows so the union eventually covers. min|N| is the lever either way.")


if __name__ == "__main__":
    main()
