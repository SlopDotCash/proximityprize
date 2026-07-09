"""
C046 probe: "Fourth-moment-can't-beat-Johnson and the period 4th moment are the SAME no-go."

The connection's testable claim (attack_plan):
  "Probe: confirm period kurtosis -> 3 at proper subgroups, certifying no L4 gain."

And the structural identity it leans on:
  Sum_b ||eta_b||^4 / Sum_b ||eta_b||^2 = E(G)/|G|   (over ALL b, including b=0)
  and the no-go S2^2 <= n*S4 (period kurtosis >= Gaussian-flat).

We test, in the PRIZE regime (dyadic mu_n PROPER subgroup, large prime p ~ n^beta, n << sqrt q):
  (1) the EXACT period moments M2 = Sum_b ||eta_b||^2 = q*|G|, M4 = Sum_b ||eta_b||^4 = q*E(G).
  (2) the period KURTOSIS over NONTRIVIAL frequencies b != 0:
         kurt_nz = ( (1/(q-1)) Sum_{b!=0} ||eta_b||^4 ) / ( (1/(q-1)) Sum_{b!=0} ||eta_b||^2 )^2
      -- this is E[X^2]/E[X]^2 of the random variable X = ||eta_b||^2; "kurtosis->3" in the
      connection's loose sense means the L4/L2 ratio of the COMPLEX gaussian-period sequence
      eta_b matches a complex-Gaussian (where E|Z|^4 / (E|Z|^2)^2 = 2 for a complex normal),
      i.e. the *normalized fourth moment* of |eta_b| over b!=0 -> 2 (complex) / 3 (real comps).
  (3) THE DECISIVE TEST of the connection's actual claim:
      does the 4th-moment LOWER bound exists_period_sq_ge (max ||eta||^2 >= (qE-n^4)/(qn-n^2))
      actually recover only Theta(n) [= "the variance"], i.e. floor/n -> O(1), NEVER n log m?
      AND is the TRUE worst period sqrt(n log m), strictly ABOVE the L4-floor? If yes, the
      "L4 returns the variance, escape is L-infinity" thesis is CONFIRMED.

Exact mod-p integer arithmetic for eta_b; double-precision only for the complex exp magnitudes
(periods are sums of <= n roots of unity, magnitudes ~ sqrt q, double is ample at these p).
"""
import cmath, math

def is_prime(N):
    if N < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if N % p == 0: return N == p
    d = N-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,N)
        if x==1 or x==N-1: continue
        for _ in range(r-1):
            x = x*x%N
            if x==N-1: break
        else: return False
    return True

def find_prime(n, beta_target):
    """smallest prime p ~ n^beta with p == 1 mod n (so mu_n exists as proper subgroup)."""
    target = int(round(n**beta_target))
    # search upward for p == 1 mod n, p prime, p >= target
    p = target - (target % n) + 1
    if p < target: p += n
    while True:
        if is_prime(p): return p
        p += n

def primitive_root(p):
    # find a generator of F_p^*
    phi = p-1
    factors = []
    m = phi; d=2
    while d*d<=m:
        if m%d==0:
            factors.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors):
            return g
    raise RuntimeError

def subgroup(p, n):
    """mu_n = unique subgroup of order n in F_p^* (n | p-1). Returns list of its elements (ints)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)   # generator of order n
    G = []
    x = 1
    for _ in range(n):
        G.append(x); x = x*h%p
    assert len(set(G))==n
    return G

def periods(p, n):
    """eta_b = sum_{y in mu_n} exp(2pi i * b*y / p), for all b in F_p. Returns list of complex."""
    G = subgroup(p,n)
    w = 2*math.pi/p
    etas = []
    # precompute exp table for residues we hit: b*y mod p
    for b in range(p):
        s = 0+0j
        for y in G:
            r = (b*y) % p
            s += cmath.exp(1j*w*r)
        etas.append(s)
    return etas

def run(n, beta, verbose=True):
    p = find_prime(n, beta)
    m = (p-1)//n
    etas = periods(p,n)
    nrm2 = [abs(z)**2 for z in etas]
    M2 = sum(nrm2)
    M4 = sum(x*x for x in nrm2)
    # exact identities: M2 should = q*|G| = p*n ; M4 = q*E(G)
    qn = p*n
    EG = M4/p   # E(G) = M4/q
    # nontrivial freqs
    nz = nrm2[1:]  # b != 0  (b=0 gives ||eta||^2 = n^2)
    qm1 = p-1
    mean2_nz = sum(nz)/qm1                       # avg ||eta||^2 over b!=0
    mean4_nz = sum(x*x for x in nz)/qm1          # avg ||eta||^4 over b!=0
    # "kurtosis" = normalized 4th moment of |eta| over b!=0 = E[|eta|^4]/E[|eta|^2]^2
    kurt = mean4_nz/(mean2_nz**2)
    # complex-Gaussian reference: for Z ~ CN, E|Z|^4 / (E|Z|^2)^2 = 2
    # exists_period_sq_ge floor on max ||eta||^2:
    floor = (p*EG - n**4)/(p*n - n**2)
    maxnz = max(nz)
    B = math.sqrt(maxnz)         # worst period magnitude
    # the connection's two competing scales:
    sqrt_n        = math.sqrt(n)
    sqrt_nlogm    = math.sqrt(n*math.log(m)) if m>1 else float('nan')
    if verbose:
        print(f"n={n:4d} p={p:>9d} beta={math.log(p)/math.log(n):.2f} m={m:>7d}")
        print(f"   M2={M2:.3f}  q*|G|={qn}   rel.err={abs(M2-qn)/qn:.2e}")
        print(f"   E(G)={EG:.3f}  (diag energy >= n^2={n*n})   E/n^2={EG/n**2:.3f}")
        print(f"   period kurtosis E|eta|^4/(E|eta|^2)^2 over b!=0 = {kurt:.4f}  (CN ref=2.0)")
        print(f"   mean ||eta||^2 over b!=0 = {mean2_nz:.3f}   ( ~ n = {n} )  ratio={mean2_nz/n:.3f}")
        print(f"   L4-floor (exists_period_sq_ge) = {floor:.3f}  floor/n={floor/n:.3f}")
        print(f"   TRUE worst B^2={maxnz:.3f}  B={B:.3f}")
        print(f"     B/sqrt(n)        = {B/sqrt_n:.3f}")
        print(f"     B/sqrt(n log m)  = {B/sqrt_nlogm:.3f}")
        print(f"     sqrt(floor)/sqrt(n) = {math.sqrt(floor)/sqrt_n:.3f}   B/sqrt(floor)={B/math.sqrt(floor):.3f}")
    return dict(n=n,p=p,m=m,kurt=kurt,floor=floor,maxnz=maxnz,B=B,
                ratio_floor_n=floor/n, B_over_sqrtn=B/sqrt_n,
                B_over_sqrtnlogm=(B/sqrt_nlogm), mean2_nz=mean2_nz, EG=EG,
                M2relerr=abs(M2-qn)/qn)

if __name__=="__main__":
    print("="*78)
    print("C046: period kurtosis & the L4-floor-vs-true-max no-go (prize regime, proper mu_n)")
    print("="*78)
    cases = [(8,4.0),(8,5.0),(16,4.0),(16,4.5),(32,3.6),(32,4.0),(64,3.2)]
    rows=[]
    for n,beta in cases:
        rows.append(run(n,beta)); print()
    print("="*78)
    print("SUMMARY: does L4 'return the variance' (floor=Theta(n)) while true max = sqrt(n log m)?")
    print(f"{'n':>4} {'p':>9} {'m':>7} {'kurt':>6} {'floor/n':>8} {'B/sqn':>7} {'B/sq(nlogm)':>11} {'B/sqfloor':>9}")
    for r in rows:
        print(f"{r['n']:>4} {r['p']:>9} {r['m']:>7} {r['kurt']:>6.3f} "
              f"{r['ratio_floor_n']:>8.3f} {r['B_over_sqrtn']:>7.3f} "
              f"{r['B_over_sqrtnlogm']:>11.3f} {r['B']/math.sqrt(r['floor']):>9.3f}")
    print()
    print("Interpretation key:")
    print(" - kurt ~ 2 (not exploding with m): period family L4/L2 is Gaussian-flat -> NO L4 localization.")
    print(" - floor/n ~ O(1): the 4th-moment LOWER bound recovers ONLY the variance scale (Theta(n)).")
    print(" - B/sq(nlogm) ~ O(1) BOUNDED while B/sqfloor GROWS with m: true max is sqrt(n log m) >> L4-floor")
    print("   => the escape above Johnson/variance is L-infinity (max over m), invisible to L4. Thesis CONFIRMED if so.")
