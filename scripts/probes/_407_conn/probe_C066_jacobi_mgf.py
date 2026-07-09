#!/usr/bin/env python3
"""
C066 attack probe (#407).

Connection C066 claims:
  - KU's Wasserstein bound is vacuous at prize scale (proven in KowalskiUntrauBarrier.lean).
  - The SalemZygmund chaining route needs only ONE exponential moment (the MGF) of the
    directional projection Re(zeta-bar * eta_c), NOT full equidistribution.
  - Via the identity I3/I4 (A_h = m*conj(tau_h)*T_h, |tau_h|=sqrt(p);  T_h=(1/m)sum_i J(chi^i,chi^h)),
    that fluctuation is "governed by" the Jacobi-sum average T_h.
  - So the missing input is an EFFECTIVE MGF bound for T_h, "strictly weaker than KU's
    Wasserstein, on F19 (Deligne-Katz monodromy) not BGK."

THE TEST. The chaining route's SubGaussianMGF is a hypothesis on the empirical MGF of
   X_zeta(c) = Re(zeta-bar * eta_c)  over the m cosets c.
The proposed substitute is an MGF on the Jacobi-average T_h.  We check whether these are
the SAME object (welds back to BGK / Gauss-period house) or a genuinely WEAKER one.

Key structural fact: the autocorrelation A_h is the DFT spectrum of |eta_b|^2 (identity I2),
and A_h = m*conj(tau_h)*T_h with |tau_h|=sqrt(p).  Hence
   |T_h| = |A_h| / (m*sqrt(p)),
so the sequence (|T_h|)_h is, up to the FLAT factor m*sqrt(p), the power spectrum of the same
Gauss-period family (eta_b).  Concretely we measure, at PROPER-SUBGROUP / prize-like params:

 (1) does max_h |T_h|/sqrt(n) track B/sqrt(n) (= they grow together => SAME wall = BGK), or
     does |T_h| stay O(1)*sqrt(n) (bounded tail const) while B grows (=> genuinely weaker)?
 (2) the empirical sub-Gaussian tail constant of the T_h family vs the eta_c family: do they
     coincide? If yes the "Jacobi-average MGF" hypothesis is literally the eta MGF hypothesis.
 (3) Does an effective T_h-MGF bound IMPLY the eta-MGF? (the proposed Lean implication).
     We check the variances:  Var_h(|T_h|^2-ish) and Var_c(eta) Parseval-tie.
"""
import cmath, math
import sympy

def primitive_root(p):
    return int(sympy.primitive_root(p))

def run(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    def psi(x): return cmath.exp(2j*math.pi*(x % p)/p)
    dlog=[0]*p; cur=1
    for k in range(p-1):
        dlog[cur]=k; cur=(cur*g)%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    # Gauss periods eta_c, c = exponent of coset rep b=g^c, c=0..m-1
    def eta(c):
        b=pow(g,c,p)
        return sum(psi((b*w)%p) for w in mu)
    etas=[eta(c) for c in range(m)]
    B=max(abs(e) for e in etas)              # the Gauss-period house (BGK object)
    # tangent sums T_h
    def T(h): return sum(chi_pow(h,(1-w)%p) for w in mu)
    Th=[T(h) for h in range(m)]
    maxT=max(abs(Th[h]) for h in range(1,m)) if m>1 else abs(Th[0])
    # tail constant for a family of complex values (max over net of directions):
    def subgauss_proxy_over_n(vals):
        # worst-direction MGF proxy / n  (same recipe as the Lean SubGaussianMGF)
        dirs=[cmath.exp(2j*math.pi*t/24) for t in range(24)]
        lambdas=[0.25,0.5,0.75,1.0,1.5,2.0]
        worst=0.0
        for zeta in dirs:
            X=[(zeta.conjugate()*v).real for v in vals]
            mu0=sum(X)/len(X); Xc=[x-mu0 for x in X]
            for lam in lambdas:
                M=sum(math.exp(lam*x) for x in Xc)/len(Xc)
                need=2*math.log(M)/(lam*lam) if M>0 else 0.0
                worst=max(worst,need)
        return worst
    proxy_eta=subgauss_proxy_over_n(etas)/n
    # For T_h: its natural scale is sqrt(n) too (T_h ~ subgroup char sum of size n).
    proxy_T=subgauss_proxy_over_n(Th)/n
    lawln=math.sqrt(n*math.log(max(m,2)))
    return dict(p=p,n=n,m=m,B=B,maxT=maxT,
                B_over_sqrtn=B/math.sqrt(n),
                maxT_over_sqrtn=maxT/math.sqrt(n),
                C_house=B/lawln, C_tangent=maxT/lawln,
                proxy_eta=proxy_eta, proxy_T=proxy_T)

def proper_subgroup_primes(n,count,start_k=2):
    """primes p = k*n+1 with k>=2 (PROPER subgroup: n | p-1 strictly, m=k>=2) and m>=8."""
    out=[]; k=start_k
    while len(out)<count:
        p=k*n+1
        if k>=8 and sympy.isprime(p):   # m=k>=8, large index = proper subgroup, many primes ok
            out.append((p,k))
        k+=1
    return out

if __name__=="__main__":
    print("# C066: is the Jacobi-average T_h MGF the SAME object as the Gauss-period eta MGF?\n")
    print("PROPER-SUBGROUP regime (m=index>=8, n<<p). If B and max|T_h| grow TOGETHER and the")
    print("two sub-Gaussian proxies COINCIDE, the 'effective Jacobi-average MGF' = the eta MGF")
    print("= the BGK/Paley wall (no relocation). Bounded-AND-different => genuine weaker input.\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'B':>7} {'max|T|':>7} | {'B/√n':>6} {'maxT/√n':>7} | "
          f"{'Chouse':>6} {'Ctang':>6} | {'proxy_eta/n':>11} {'proxy_T/n':>9}")
    for n in [8,16,32,64]:
        ps=proper_subgroup_primes(n,6,start_k=8)
        # also push m larger for the same n to see m-trend
        ps+=proper_subgroup_primes(n,2,start_k=300)
        for (p,k) in ps:
            if p>250000:  # keep exact double loops tractable
                continue
            r=run(p,n)
            print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['B']:>7.3f} {r['maxT']:>7.3f} | "
                  f"{r['B_over_sqrtn']:>6.2f} {r['maxT_over_sqrtn']:>7.2f} | "
                  f"{r['C_house']:>6.3f} {r['C_tangent']:>6.3f} | "
                  f"{r['proxy_eta']:>11.3f} {r['proxy_T']:>9.3f}")
    print("\nREAD: if maxT/√n tracks B/√n (both bounded, ratio ~const) => T_h is the SAME spectral")
    print("object as eta (Fourier dual via |T_h|=|A_h|/(m√p)); the 'weaker MGF' is illusory.")
    print("If proxy_T/n stays ~O(1) exactly where proxy_eta/n does, the two MGF hypotheses coincide.")
