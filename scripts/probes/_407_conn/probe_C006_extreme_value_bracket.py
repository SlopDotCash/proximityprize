#!/usr/bin/env python3
"""
C006 attack: "Johnson-vs-capacity gap is an EXTREME-VALUE gap; in-tree code brackets the
worst period in [sqrt(n), sqrt(n log m)]; only open input = a SINGLE MGF (one exponential
moment), strictly less than the BGK all-moments wall."

THREE precise sub-claims to test EXACTLY (prize regime: n=2^mu thin, q ~ n^beta, beta~4-5):

  (A) LOWER ENDPOINT.  exists_period_sq_ge proves
        max_{b!=0} ||eta_b||^2 >= (q E - |G|^4)/(q|G| - |G|^2).
      Claim: this floor ~ |G| = n, i.e. the proven lower endpoint is exactly sqrt(n)
      (NOT already sqrt(n log m)).  Compute the EXACT rational floor and floor/n.

  (B) UPPER ENDPOINT validity.  Claim: B = max_c ||eta_c|| <= sqrt(2 sigma^2 log m) with
      sigma^2 = O(n).  Measure the SMALLEST sigma^2 that makes the Chernoff ceiling
      sqrt(2 sigma^2 log m) actually >= the true B.  Call it sigma2_needed_ceiling.
      If sigma2_needed/n blows up with m (or with beta), the "sigma^2=O(n)" upper endpoint
      is FALSE in regime and the bracket does not hold.

  (C) THE CRUX: is the single MGF genuinely weaker than all-moments?
      The Chernoff step needs the MGF at the OPTIMAL lambda* = sqrt(2 log m / sigma^2).
      That lambda* GROWS with log m.  Test whether the empirical MGF
        Mhat(lambda) = (1/m) sum_c exp(lambda Re(zeta-bar eta_c))
      satisfies Mhat(lambda) <= exp(sigma^2 lambda^2/2) with a FIXED sigma^2=O(n)
      AT lambda = lambda*(m).  i.e. measure sigma2_mgf(lambda*) = 2 log Mhat(lambda*)/lambda*^2.
      KEY DISTINCTION:
        - if sigma2_mgf(lambda*)/n stays O(1) as m grows  => single MGF really IS the only
          input and it is bounded => REDUCED (genuine relocation off all-moments).
        - if sigma2_mgf(lambda*)/n GROWS with log m (the MGF fattens at the large lambda the
          max needs) => the single-MGF input is NOT weaker; controlling it at lambda* is
          EQUIVALENT to controlling the high moments => welds back to BGK => OPEN(W-BGK).
      The whole insight of C006 lives or dies here.

All EXACT where it matters: floor (A) is exact rational; (B),(C) use full Gauss-period
computation (exact integer mod-p, complex exp to double precision; m,p modest but n thin,
beta>=2 with several proper-subgroup large-ish primes).
"""
import cmath, math
from fractions import Fraction

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = []; t = phi; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    return None

def subgroup(p, n, g):
    m = (p-1)//n
    gen = pow(g, m, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    return mu, m

def additive_energy(mu, p):
    """E(G) = #{(a,b,c,d) in G^4 : a+b = c+d (mod p)}. Exact integer count."""
    from collections import Counter
    cnt = Counter()
    for a in mu:
        for b in mu:
            cnt[(a+b) % p] += 1
    return sum(v*v for v in cnt.values())

def gauss_periods(p, mu, g, m):
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []
    bc = 1
    for c in range(m):
        s = 0j
        for x in mu:
            s += e[(bc*x) % p]
        etas.append(s)
        bc = (bc*g) % p
    return etas

def lower_floor_exact(p, mu):
    """exists_period_sq_ge floor = (q*E - |G|^4)/(q*|G| - |G|^2), exact Fraction."""
    n = len(mu); q = p
    E = additive_energy(mu, p)
    num = Fraction(q*E - n**4)
    den = Fraction(q*n - n*n)
    return num/den, E

def main():
    print("# C006 extreme-value bracket attack (prize regime: thin n, q~n^beta, several primes)")
    print()
    print("## (A) LOWER ENDPOINT  floor=(qE-n^4)/(qn-n^2)  [exact];  expect floor/n ~ 1 (=> sqrt(n) not sqrt(n log m))")
    print(f"{'p':>8} {'n':>4} {'m':>5} {'beta':>5} | {'E':>8} {'E/n^2':>7} | {'floor':>9} {'floor/n':>8} {'sqrt(floor)/sqrt(n)':>18}")
    rows_A = []
    # pick thin n with several primes, growing beta = log_n p
    targets = []
    for n in [8, 16, 32]:
        # gather primes p=1 mod n across a range of beta
        found = 0
        p = n
        while found < 8:
            p += 1
            if p % n != 1: continue
            if not is_prime(p): continue
            m = (p-1)//n
            if m < 4: continue
            if p > 90000: break
            beta = math.log(p)/math.log(n)
            # keep a spread of beta values, want some with n << sqrt(p) i.e. beta>=2.5+
            targets.append((p,n,m,beta))
            found += 1
    for (p,n,m,beta) in targets:
        g = primitive_root(p)
        mu, m = subgroup(p, n, g)
        floor, E = lower_floor_exact(p, mu)
        ff = float(floor)
        print(f"{p:>8} {n:>4} {m:>5} {beta:5.2f} | {E:>8} {E/n**2:7.3f} | {ff:9.3f} {ff/n:8.4f} {math.sqrt(max(ff,0))/math.sqrt(n):18.4f}")
        rows_A.append((p,n,m,beta,ff,ff/n))

    print()
    print("## (B)+(C) UPPER ENDPOINT + CRUX MGF-at-optimal-lambda")
    print("# B=max||eta_c||; ceil_min sigma2 s.t. sqrt(2 s log m)>=B  (=sigma2_need_ceil)")
    print("# lambda*=sqrt(2 log m / sigma2);  sigma2_mgf(L*) = 2 log Mhat(L*)/L*^2  (worst dir)")
    print(f"{'p':>8} {'n':>4} {'m':>5} {'beta':>5} | {'B':>7} {'B/sqrtn':>8} {'B/sqrt(nlogm)':>13} "
          f"| {'s2need/n':>9} | {'lam*':>6} {'s2mgf(L*)/n':>12} {'logm':>6}")
    rows_BC = []
    bigger = []
    for n in [8, 16, 32]:
        cnt = 0; p = n
        while cnt < 6:
            p += 1
            if p % n != 1 or not is_prime(p): continue
            m = (p-1)//n
            if m < 16: continue
            if p > 80000: break
            beta = math.log(p)/math.log(n)
            if beta < 2.3: continue  # enforce PRIZE-like thin regime n << sqrt(p)
            bigger.append((p,n,m,beta)); cnt += 1
    for (p,n,m,beta) in bigger:
        g = primitive_root(p)
        mu, m = subgroup(p, n, g)
        etas = gauss_periods(p, mu, g, m)
        mags = [abs(e) for e in etas]
        B = max(mags)
        logm = math.log(m)
        # (B) smallest sigma^2 with sqrt(2 sigma2 logm) >= B  => sigma2 >= B^2/(2 logm)
        s2_need = B*B/(2*logm) if logm > 0 else float('inf')
        # (C) optimal lambda* depends on sigma2; use sigma2 = s2_need (the ceiling-fitting one)
        # so lambda* = sqrt(2 logm / s2_need) = 2 logm / B  (consistent w/ Chernoff optimum)
        lam_star = math.sqrt(2*logm/s2_need) if s2_need > 0 else 0.0
        # measure empirical MGF at lam_star over directions, take WORST (max) -> hardest sigma2
        import statistics as st
        worst_s2mgf = 0.0
        for t in range(24):
            zeta = cmath.exp(2j*math.pi*t/24)
            X = [(zeta.conjugate()*e).real for e in etas]
            mu_m = st.mean(X)
            Xc = [x-mu_m for x in X]   # center (DC is the c=0 trivial direction noise)
            # Mhat(lam_star)
            Mhat = st.mean(math.exp(lam_star*x) for x in Xc)
            if Mhat > 1 and lam_star > 0:
                s2 = 2*math.log(Mhat)/(lam_star*lam_star)
                worst_s2mgf = max(worst_s2mgf, s2)
        print(f"{p:>8} {n:>4} {m:>5} {beta:5.2f} | {B:7.3f} {B/math.sqrt(n):8.3f} {B/math.sqrt(n*logm):13.3f} "
              f"| {s2_need/n:9.3f} | {lam_star:6.3f} {worst_s2mgf/n:12.4f} {logm:6.2f}")
        rows_BC.append((p,n,m,beta,B,s2_need/n,lam_star,worst_s2mgf/n,logm))

    print()
    print("## CRUX verdict aid: does s2mgf(L*)/n grow with log m at fixed n? (regress per n)")
    by_n = {}
    for (p,n,m,beta,B,s2n,lam,s2mgf,logm) in rows_BC:
        by_n.setdefault(n, []).append((logm, s2mgf))
    for n in sorted(by_n):
        pts = sorted(by_n[n])
        if len(pts) >= 2:
            xs = [x for x,_ in pts]; ys = [y for _,y in pts]
            xb = sum(xs)/len(xs); yb = sum(ys)/len(ys)
            num = sum((x-xb)*(y-yb) for x,y in pts)
            den = sum((x-xb)**2 for x in xs)
            slope = num/den if den>0 else float('nan')
            print(f" n={n}: s2mgf(L*)/n vs log m  slope={slope:+.4f}  range=[{min(ys):.3f},{max(ys):.3f}]  (lam* range [{0:.2f}..])")
    print()
    print("# READ: slope ~ 0 and s2mgf(L*)/n bounded  => single MGF really bounded at the needed lambda => REDUCED.")
    print("#       slope > 0 (s2mgf fattens at lam*)   => controlling MGF at lam* == high-moment control => welds to BGK => OPEN.")

if __name__ == "__main__":
    main()
