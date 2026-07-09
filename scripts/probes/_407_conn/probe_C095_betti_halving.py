#!/usr/bin/env python3
"""
probe_C095_betti_halving.py  (#407 connection C095)

CLAIM (C095): the forced involution w |-> w^{-1} on the tangent set {1-w : w in mu_n}
(via the identity 1-w^{-1} = -w^{-1}(1-w), with -w^{-1} in mu_n when n even) makes
T_h = sum_{w in mu_n} chi^h(1-w) FACTOR THROUGH the quotient mu_n/<w |-> -w> = the SQUARES
of the tangent values. The asserted consequence: the cohomological/Betti curve degree HALVES
from n to n/2, so the GLT/Hasse-Weil r=2 moment result extends to r=3, pushing the moment-method
crossover r* from ~3 toward higher r (a structural degree reduction on the tangent face).

We test, at PROPER-SUBGROUP large primes (n << sqrt(q), n=2^mu, dyadic), the FALSIFIABLE pieces:

  TEST 1 (the factorization claim, the crux):
     Does the involution make chi^h(1-w) constant on involution orbits?
     Compute the multiplier  mu_w := chi^h(1-w^{-1}) / chi^h(1-w) = chi^h(-w^{-1}).
     If C095's "factors through the quotient" is right, T_h should reduce to a sum over n/2 orbits
     with each orbit contributing a CONSTANT (mu_w == 1). Measure how often mu_w == 1.

  TEST 2 (the only-genuine reduction: a real sum over n/2 terms):
     The honest content of an involution acting on a character sum is the PLUS/MINUS eigenspace
     split:  T_h = (1/2) sum_w [ chi^h(1-w) + chi^h(1-w^{-1}) ]
                 = (1/2) sum_w chi^h(1-w) [ 1 + chi^h(-w^{-1}) ].
     This is exact but does NOT reduce the number of distinct curve-degree terms unless the
     bracket has special structure. Verify the identity exactly and check whether the bracket
     [1 + chi^h(-w^{-1})] collapses the support (genuinely halving the # of nonzero terms).

  TEST 3 (the DECISIVE quantitative test -- the moment crossover):
     The moment method gives  B <= (m * E_r)^{1/(2r)}  with E_r the 2r-th additive energy of mu_n
     (equivalently V_{2r}/m). The Betti/Hasse-Weil "validity" of the Gaussian value
     E_r ~ (2r-1)!! n^r holds while the FERMAT-curve point count is the diagonal value, i.e.
     up to r_max set by the curve degree d. C095 claims d halves (n -> n/2) so r_max should
     roughly DOUBLE (the # of moments the curve count certifies as Gaussian).
     We measure E_r(mu_n) DIRECTLY (exact integer count) and compare:
       (i) ratio E_r / ((2r-1)!! n^r)  -- is it ~1 (Gaussian, "Betti clean") to a LARGER r
           for 2-power mu_n than the deg-n prediction, as if the curve were deg n/2?
       (ii) does the 2-power (antipodal) structure LOWER E_r (as a degree-halving would) or
            RAISE it (the documented "antipodal -1 ADDS solutions" Wall-G)?
     Compare 2-power mu_n against an odd-order subgroup of the SAME size class as control.
"""
import itertools, math
from collections import Counter

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(a,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True

def subgroup(p,n):
    """order-n multiplicative subgroup of F_p^*, plus a generator g of F_p^* (for characters)."""
    for g in range(2,p):
        # check g is a primitive root by order check on the n-part is not enough; we just need
        # an element h of order exactly n:
        h=pow(g,(p-1)//n,p)
        s=set(); x=1
        for _ in range(n):
            s.add(x); x=x*h%p
        if len(s)==n:
            return sorted(s), h
    return None,None

def primitive_root(p):
    fac=[]
    m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):
            return g
    return None

def tangent_sum_and_involution(p,n,hexp):
    """T_h with chi a char of order m=(p-1)/n; chi^h applied to 1-w over w in mu_n.
       chi defined via discrete log base primitive root g0: chi(g0^k)=zeta_m^k, order m=(p-1)/n.
       chi^h(y) = zeta_{?}^{...}; we represent character values as exponents mod (p-1)/?.
       Simpler: chi has order m, chi(x) = e(  (m/(p-1)) * dlog_{g0}(x) ) ... we just track the
       ANGLE exponent e in Z/(p-1) where chi^h(x) = exp(2pi i * (h * (p-1)/m_index_step) ... )
       To avoid confusion, build chi directly: let g0 primitive root, chi(g0^k) = w_m^k with
       w_m a primitive m-th root, m = (p-1)/n. So chi(x)=w_m^{ dlog(x) }, and chi has order m.
       chi^h(x) = w_m^{ h*dlog(x) }.  Tangent values 1-w are units (w!=1 excluded; w=1 gives 0).
    """
    mu,h = subgroup(p,n)
    g0 = primitive_root(p)
    m = (p-1)//n
    # discrete log table
    dlog = {}
    x=1
    for k in range(p-1):
        dlog[x]=k
        x=x*g0%p
    import cmath
    wm = cmath.exp(2j*math.pi/m)
    def chi_h(y):
        y%=p
        if y==0: return 0.0+0.0j
        return wm**((hexp*dlog[y]) % m)
    # T_h
    T = 0j
    nonzero_terms = 0
    for w in mu:
        if w==1: continue
        val = chi_h((1-w)%p)
        T += val
        if abs(val)>1e-9: nonzero_terms+=1
    # TEST 1: multiplier on involution orbits: chi^h(1-w^{-1})/chi^h(1-w) = chi^h(-w^{-1})
    mults = []
    mult_is_one = 0
    total_pairs = 0
    for w in mu:
        if w==1: continue
        winv = pow(w,p-2,p)
        if winv==1: continue
        num = chi_h((1 - winv)%p)
        den = chi_h((1 - w)%p)
        if abs(den)<1e-12: continue
        mlt = num/den
        # also the predicted factorization multiplier chi^h(-w^{-1}):
        pred = chi_h((-winv)%p)
        mults.append((mlt,pred))
        total_pairs+=1
        if abs(mlt-1.0)<1e-9: mult_is_one+=1
    # check 1-w^{-1} = -w^{-1}(1-w) exactly (integer), and -w^{-1} in mu_n:
    id_ok = True
    neg_inv_in_mu = 0
    mu_set=set(mu); checks=0
    for w in mu:
        if w==1: continue
        winv=pow(w,p-2,p)
        lhs=(1-winv)%p
        rhs=((-winv)*(1-w))%p
        if lhs!=rhs: id_ok=False
        if ((-winv)%p) in mu_set: neg_inv_in_mu+=1
        checks+=1
    return dict(p=p,n=n,m=m,T=T,absT=abs(T),
                nonzero_terms=nonzero_terms, n_terms_total=n-1,
                pairs=total_pairs, mult_is_one=mult_is_one,
                frac_mult_one=mult_is_one/max(total_pairs,1),
                identity_exact=id_ok, neg_inv_in_mu=neg_inv_in_mu, neg_inv_checks=checks)

def energy_Er(p,n,r):
    """exact 2r-th additive energy E_r(mu_n) = #{(a_1..a_r,b_1..b_r) in mu_n^{2r} :
       a_1+...+a_r = b_1+...+b_r}.  Computed via sum over multiplicities of r-fold sums.
       Only feasible for small n; use convolution of the indicator of r-fold sumset multiplicity.
    """
    mu,_ = subgroup(p,n)
    # r-fold sum multiplicity vector over Z/p
    from collections import Counter
    cur = Counter({0:1})
    for _ in range(r):
        nxt = Counter()
        for s,c in cur.items():
            for a in mu:
                nxt[(s+a)%p]+= c
        cur=nxt
    E = sum(c*c for c in cur.values())
    return E

if __name__=="__main__":
    print("# C095 probe: tangent-set involution -> Betti/degree halving? (#407)")
    print("# PRIZE REGIME: dyadic n=2^mu PROPER subgroup, n << sqrt(q), large prime, multiple primes.\n")

    print("="*78)
    print("TEST 1+2: the involution factorization claim (crux)")
    print("  multiplier  chi^h(1-w^-1)/chi^h(1-w)  should be IDENTICALLY 1 if T_h 'factors")
    print("  through the quotient mu_n/{+-1}'. Predicted multiplier = chi^h(-w^-1).")
    print("="*78)
    print(f"{'p':>7} {'n':>4} {'m':>6} {'h':>3} | {'identity':>8} {'-w^-1 in mu':>11} | {'frac mult==1':>13} | {'|T_h|':>8} {'|T|/sqrt(n)':>11}")
    # proper-subgroup dyadic primes: n=2^mu, pick p with n | p-1, p > n^2 (proper, n<sqrt q)
    for n in [8,16,32,64]:
        cnt=0; k=2
        while cnt<3:
            p=k*n+1; k+=1
            if p > 60000: break
            if is_prime(p) and p > n*n:   # proper subgroup, n < sqrt(p)
                for hexp in [1]:           # nontrivial h (chi^h nontrivial as long as h !=0 mod m)
                    r=tangent_sum_and_involution(p,n,hexp)
                    print(f"{p:>7} {n:>4} {r['m']:>6} {hexp:>3} | {str(r['identity_exact']):>8} "
                          f"{r['neg_inv_in_mu']}/{r['neg_inv_checks']:<5} | "
                          f"{r['frac_mult_one']:>13.3f} | {r['absT']:>8.3f} {r['absT']/math.sqrt(n):>11.3f}")
                cnt+=1
    print()
    print("INTERPRETATION TEST1: identity is an EXACT algebraic fact (expect True always).")
    print("  But 'frac mult==1' measures whether chi^h(1-w) is CONSTANT on involution orbits.")
    print("  C095 needs ~1.0 (factors through quotient).  If ~0, T_h does NOT factor: claim FALSE.")
    print()

    print("="*78)
    print("TEST 3: the DECISIVE moment-crossover test")
    print("  E_r(mu_n) exact vs Gaussian (2r-1)!! n^r.  Betti-clean ratio ~1.")
    print("  C095: degree halving n->n/2 would EXTEND the clean range to larger r (~double r_max).")
    print("  Wall-G: antipodal -1 RAISES E_r (ratio grows in r). Which wins?")
    print("="*78)
    def dfact(r):  # (2r-1)!!
        v=1
        for i in range(1,2*r,2): v*=i
        return v
    for n in [8,16]:
        # pick a proper-subgroup prime n<sqrt(p)
        p=None; k=2
        while True:
            cand=k*n+1; k+=1
            if cand>n*n*4 and is_prime(cand) and cand>n*n:
                p=cand; break
            if cand>200000: break
        if p is None: continue
        print(f"\n  n={n}  p={p}  m={(p-1)//n}  (2-power dyadic subgroup)")
        print(f"    {'r':>2} {'E_r':>12} {'(2r-1)!!n^r':>14} {'ratio':>8}")
        for r in range(2,7):
            Er=energy_Er(p,n,r)
            gauss=dfact(r)*(n**r)
            print(f"    {r:>2} {Er:>12} {gauss:>14} {Er/gauss:>8.3f}")
    # ODD control of comparable size to test whether 2-power structure halves anything
    print("\n  CONTROL: odd-order subgroup (no antipodal -1), comparable n:")
    for n in [9,15]:
        p=None; k=2
        while True:
            cand=k*n+1; k+=1
            if cand>n*n*4 and is_prime(cand) and cand>n*n:
                p=cand; break
            if cand>200000: break
        if p is None: continue
        print(f"\n  n={n}  p={p}  m={(p-1)//n}  (ODD-order subgroup, no -1)")
        print(f"    {'r':>2} {'E_r':>12} {'(2r-1)!!n^r':>14} {'ratio':>8}")
        for r in range(2,7):
            Er=energy_Er(p,n,r)
            gauss=dfact(r)*(n**r)
            print(f"    {r:>2} {Er:>12} {gauss:>14} {Er/gauss:>8.3f}")
