#!/usr/bin/env python3
r"""
probe_largesieve_avgq_deep_407.py  --  #407: AVERAGE-OVER-q, in the REGIME WHERE DEFECTS EXIST.

The shallow probe (probe_largesieve_avgq_407) found D(q)=0 for ALL q at beta=4: in that regime q is
above the norm threshold (|N(alpha)| <= (2r)^{phi} < q for these tiny r), so NO defect can occur.
That is the PROVEN norm-regime (kappa_r<=1 holds trivially). The prize is HARD precisely where
r ~ ln q is large enough that the norm threshold (2r)^{phi/2} EXCEEDS q -- then defects can appear.

To test the average-over-q claim HONESTLY we must work where D(q)>0 for SOME q. Two ways to enter it:
  (A) push r up so (2r)^{phi/2} > q  (deep moments) -- expensive (n^{2r} pairs);
  (B) shrink q (shallow primes q ~ n^2..n^3) so the norm threshold bites at small r.
Both are the SAME phenomenon (the norm threshold = q ~ (2r)^{phi/2}). We use (B): fix r where the
char-0 alphas have norms straddling q, scan many primes q across that band, and measure:
   - the per-q defect count D(q) and the fraction of GOOD q;
   - the FIRST MOMENT  M1 = (1/#Q) sum_q D(q)  and its decomposition over alpha
       (D(q)=sum_alpha mult(alpha)*[q | alpha]);  M1 = sum_alpha mult(alpha)* (#{q: q|alpha}/#Q);
   - which alpha dominate M1 (the heavy tail: alpha with MANY prime divisors in the window);
   - the SECOND MOMENT  M2 = (1/#Q) sum_q D(q)^2  and Var; Chebyshev -> P(D > t) <= Var/(t-M1)^2;
   - whether a GOOD q (D<=baseline, ideally D=0) EXISTS and how common.

KEY large-sieve fact being tested:  for FIXED alpha != 0, #{q in [Q,2Q], q=1 mod n : q | alpha}
   <= #{q | N(alpha)} <= log|N(alpha)| / log Q <= phi(n)*log(2r)/log Q.   (a fixed alpha has FEW bad q)
So M1 = sum_alpha mult(alpha) * O(phi log(2r)/(#Q log Q)).  The question is whether the SUM over the
many alpha (offdiag ~ n^{2r} of them) still leaves room for a good q -- i.e. whether the bad q
(each killed by its own few alpha) cover all of [Q,2Q] or leave gaps.
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

def primes_window(n, Q, count, deep=True):
    out = []
    q = Q - (Q % n) + 1
    if q < Q: q += n
    while len(out) < count:
        if q > 3 and is_prime(q) and (odd_part((q-1)//n) > 1 if deep else True):
            out.append(q)
        q += n
    return out

def reduced_vec(coeff, n):
    h = n//2
    return tuple(coeff[j] - coeff[j+h] for j in range(h))

def enumerate_reduced(n, r):
    """reduced_vec -> # ordered r-tuples giving it (char-0 sum class)."""
    red = defaultdict(int)
    for tup in itertools.combinations_with_replacement(range(n), r):
        coeff = [0]*n
        for t in tup: coeff[t] += 1
        cc = Counter(tup)
        num = math.factorial(r); den = 1
        for v in cc.values(): den *= math.factorial(v)
        mult = num//den
        red[reduced_vec(coeff, n)] += mult
    return red

def alpha_value_mod_q(alpha, zpows, q):
    val = 0
    for j, a in enumerate(alpha):
        if a: val += a*zpows[j]
    return val % q

def integer_norm_bound(alpha):
    """L2^2 of reduced coeffs -> AM-GM upper bound on |N(alpha)| = (L2^2)^{phi/2} (rough)."""
    return sum(a*a for a in alpha)


def run(n, r, beta_lo, beta_hi, nprimes):
    h = n//2
    print(f"\n{'#'*90}\n n={n}, r={r}  band q in [n^{beta_lo}, n^{beta_hi}]   (norm threshold ~ (2r)^(phi/2)=2^{0.5*h*math.log2(2*r):.1f})\n{'#'*90}")
    red = enumerate_reduced(n, r)
    red_items = list(red.items())
    Er0 = sum(v*v for v in red.values())
    offdiag = n**(2*r) - Er0
    # distinct nonzero alpha and multiplicities
    alpha_mult = defaultdict(int)
    for (rv1, w1) in red_items:
        for (rv2, w2) in red_items:
            alpha = tuple(rv1[j]-rv2[j] for j in range(h))
            if any(alpha):
                alpha_mult[alpha] += w1*w2
    alphas = list(alpha_mult.keys())
    mults = [alpha_mult[a] for a in alphas]
    print(f"  E_r^0={Er0}, offdiag pairs={offdiag}, distinct nonzero alpha={len(alphas)}")
    # norm magnitude distribution of alpha (L2^2):
    l2s = sorted(integer_norm_bound(a) for a in alphas)
    print(f"  alpha L2^2 (reduced coeffs): min={l2s[0]}, median={statistics.median(l2s)}, max={l2s[-1]}")

    # window of primes spanning the band
    Q = int(round(n**beta_lo))
    Qhi = int(round(n**beta_hi))
    # gather primes up to Qhi
    qs = []
    q = Q - (Q % n) + 1
    if q < Q: q += n
    while q <= Qhi and len(qs) < nprimes:
        if q > 3 and is_prime(q) and odd_part((q-1)//n) > 1:
            qs.append(q)
        q += n
    if len(qs) < 5:
        qs = primes_window(n, Q, nprimes)
    print(f"  scanning {len(qs)} primes q in [{qs[0]}, {qs[-1]}] (2^{math.log2(qs[0]):.1f}..2^{math.log2(qs[-1]):.1f})")

    # per-q defect count + per-alpha bad-q count (first moment decomposition)
    Dvals = []
    alpha_badq = defaultdict(int)   # alpha -> # bad q in window
    nq = len(qs)
    for q in qs:
        z = order_n_root(q, n)
        zpows = [pow(z, j, q) for j in range(h)]
        D = 0
        for a, m in zip(alphas, mults):
            if alpha_value_mod_q(a, zpows, q) == 0:
                D += m
                alpha_badq[a] += 1
        Dvals.append(D)

    baseline = offdiag / statistics.median(qs)
    M1 = statistics.mean(Dvals)
    M2 = statistics.mean(d*d for d in Dvals)
    var = M2 - M1*M1
    n_good = sum(1 for d in Dvals if d <= baseline)
    n_zero = sum(1 for d in Dvals if d == 0)
    mx = max(Dvals)
    print(f"  baseline (offdiag/q) ~ {baseline:.4f}")
    print(f"  D(q): min={min(Dvals)} median={statistics.median(Dvals)} mean(M1)={M1:.4f} max={mx}")
    print(f"  #q D==0: {n_zero}/{nq} ({100*n_zero/nq:.1f}%)   #q GOOD(D<=baseline): {n_good}/{nq} ({100*n_good/nq:.1f}%)")
    print(f"  SECOND MOMENT M2={M2:.3f}, Var={var:.3f}, std={math.sqrt(max(var,0)):.3f}")
    if var > 0 and mx > M1:
        cheb = var/((mx-M1)**2) if mx>M1 else float('inf')
        print(f"  Chebyshev: P(D>={mx}) <= Var/(mx-M1)^2 = {cheb:.4f}  (empirical {sum(1 for d in Dvals if d==mx)/nq:.4f})")
    # heavy-tail: how many alpha have >=1 bad q, and the worst ones
    n_alpha_withbad = sum(1 for a in alphas if alpha_badq[a] > 0)
    worst = sorted(alphas, key=lambda a: -alpha_badq[a])[:5]
    print(f"  FIRST-MOMENT decomposition: {n_alpha_withbad}/{len(alphas)} alpha have >=1 bad q.")
    print(f"     M1 = sum_a mult(a)*(#badq(a)/nq). Worst alpha (by #badq):")
    for a in worst:
        if alpha_badq[a] == 0: break
        print(f"        alpha={a}  L2^2={integer_norm_bound(a)}  mult={alpha_mult[a]}  #badq={alpha_badq[a]}  "
              f"(frac {alpha_badq[a]/nq:.4f})  contrib to M1={alpha_mult[a]*alpha_badq[a]/nq:.4f}")
    # the large-sieve heart: does the heavy-tail (few alpha with many bad q) ruin EVERY q, or are
    # the bad q sparse enough that a good q exists?
    print(f"  => GOOD q exists: {n_zero>0} (D==0)  or {n_good>0} (D<=baseline). "
          f"Fraction of bad q (D>baseline): {1-n_good/nq:.4f}")
    return n_zero, nq


def main():
    print("="*92)
    print(" #407 AVERAGE-OVER-q, DEEP/SHALLOW regime where defects EXIST")
    print("="*92)
    # n=8: phi=4. norm threshold (2r)^2. For defects need q < (2r)^2:
    #   r=2: thr=16 (q>16 always -> no defect, confirmed). r=3: thr=36. r=4: thr=64.
    #   r=6: (12)^2=144. To get q < thr=144 with q=1 mod 8 deep: q in {17,41,73,89,97,...} -- shallow.
    # Better: n=4 (phi=2), threshold (2r)^1=2r. r=4 -> thr=8 (too small). Use n=8 shallow band.
    run(8, 3, 1.0, 2.5, 200)    # q ~ 8..180: r=3 threshold 36
    run(8, 4, 1.0, 2.5, 200)    # q ~ 8..180: r=4 threshold 64 (more defects)
    run(8, 5, 1.0, 3.0, 300)    # q up to 512: r=5 thr=100
    run(8, 6, 1.0, 3.5, 400)    # q up to ~1400: r=6 thr=144
    # n=16: phi=8. threshold (2r)^4. r=2 -> 4^4=256. so q<256 can defect at r=2!
    run(16, 2, 1.0, 2.5, 300)   # q ~ 16..1024: r=2 thr=256


if __name__ == "__main__":
    main()
