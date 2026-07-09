#!/usr/bin/env python3
"""
C059 part 2: drive the anomaly NONZERO (box meets prime) and measure C059-bound usefulness.

To get a nonzero char-p energy anomaly we need (2r)^{phi(n)} >= q (box meets the prime sublattice).
We hold a PROPER subgroup mu_n (n=2^mu | q-1, large prime, n << sqrt(q)) but choose r large enough
(or q at the small end of the prize band) that spurious p|N(alpha) collisions appear.

We then test the ACTUAL content of C059:
  anomaly  <=  R_r(0) * (#contributing cyclotomic states alpha != 0 with p | N(alpha))   [C059 bound]
and ask:
  - is the bound TRUE? (it must be, since each contributing state contributes <= R_r(0) by the cap;
    actually each contributes its OWN diff-mass, which is <= R_r(0); we verify)
  - is it USEFUL? compare bound vs anomaly vs E_r^char0. The autocorr brick caps each term by R_r(0)
    ~ n^r = the ENTIRE energy. So bound ~ (n^r) * (#contrib). For the bound to beat the trivial
    "anomaly <= E_r^Fp" we'd need #contrib * R_r(0) < E_r^Fp, i.e. #contrib < 1, i.e. NO contributors.
    => the autocorr cap is only non-vacuous when the count is 0 (clean range). Test this directly.
"""
import itertools, math
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def find_prime_1modn(n, lo):
    q = lo - (lo % n) + 1
    if q < lo: q += n
    while not is_prime(q): q += n
    return q

def subgroup_mu_n(q,n):
    e=(q-1)//n
    for c in range(2,q):
        h=pow(c,e,q)
        if h==1: continue
        S=set(); x=1
        for _ in range(n):
            x=(x*h)%q; S.add(x)
        if len(S)==n: return sorted(S), h
    raise RuntimeError

def char0_sumr(n, r):
    """r-fold sum distribution over Z[zeta_n], n=2^mu. coords in basis {1..x^{n/2-1}}, Phi_n=x^{n/2}+1."""
    half=n//2
    def coord(e):
        e%=n; v=[0]*half
        if e<half: v[e]+=1
        else: v[e-half]-=1
        return tuple(v)
    f=Counter()
    for e in range(n): f[coord(e)]+=1
    def conv(a,b):
        c=Counter()
        for x,ax in a.items():
            for y,by in b.items():
                c[tuple(p+q for p,q in zip(x,y))]+=ax*by
        return c
    s=Counter({tuple([0]*half):1})
    for _ in range(r): s=conv(s,f)
    return s, half

def analyze(n, q, r):
    mu, zeta = subgroup_mu_n(q,n)
    sumr, half = char0_sumr(n,r)
    E0 = sum(c*c for c in sumr.values())
    # char-p energy: r-fold sum over F_q then R_r(0)
    f=Counter()
    for a in mu: f[a%q]+=1
    def convq(a,b):
        c=Counter()
        for x,ax in a.items():
            for y,by in b.items():
                c[(x+y)%q]+=ax*by
        return c
    sq=Counter({0:1})
    for _ in range(r): sq=convq(sq,f)
    # E_r^Fp = R_r(0) = sum_s sq(s)^2
    Erp = sum(c*c for c in sq.values())
    anomaly = Erp - E0
    # contributing cyclotomic states: alpha = s - t (s,t in support of sumr), alpha != 0, image=0 mod q
    zpow=[pow(zeta,j,q) for j in range(half)]
    def toFq(v): return sum((c%q)*zpow[j] for j,c in enumerate(v))%q
    # difference distribution masses
    contrib_states=0; anomaly_direct=0; max_state_mass=0
    # to bound work, iterate over pairs of support states
    supp=list(sumr.items())
    for s,cs in supp:
        for t,ct in supp:
            if s==t: continue
            d=tuple(a-b for a,b in zip(s,t))
            if all(x==0 for x in d): continue
            if toFq(d)==0:
                contrib_states+=1
                anomaly_direct+=cs*ct
                if cs*ct>max_state_mass: max_state_mass=cs*ct
    R0=Erp
    c059_bound = R0 * contrib_states
    return dict(n=n,q=q,r=r,E0=E0,Erp=Erp,anomaly=anomaly,anomaly_direct=anomaly_direct,
                contrib=contrib_states,R0=R0,bound=c059_bound,max_state_mass=max_state_mass)

def report(d):
    print(f"  n={d['n']} q={d['q']} r={d['r']}  (2r)^phi={(2*d['r'])**(d['n']//2):.3e} vs q={d['q']:.3e}  meets={'YES' if (2*d['r'])**(d['n']//2)>=d['q'] else 'no'}")
    print(f"    E0={d['E0']}  E_Fp={d['Erp']}  anomaly={d['anomaly']} (direct {d['anomaly_direct']}, MATCH={d['anomaly']==d['anomaly_direct']})")
    print(f"    #contrib states={d['contrib']}   max single-state mass={d['max_state_mass']}  (R0={d['R0']})")
    print(f"    C059 bound R0*#contrib = {d['bound']}")
    if d['anomaly']>0:
        print(f"    bound/anomaly = {d['bound']/d['anomaly']:.3e}   bound/E_Fp = {d['bound']/d['Erp']:.3e}   anomaly/E_Fp = {d['anomaly']/d['Erp']:.3e}")
    print()

if __name__=="__main__":
    print("=== C059 part2: nonzero anomaly + usefulness of R0*#contrib bound (proper-subgroup primes) ===\n")
    # n=8, proper subgroup of large prime, but pick prime at SMALL end so (2r)^4 meets it.
    # q must be 1 mod 8, prime, n=8 << sqrt(q). For r=4: (8)^4=4096; choose q just below ~4096 region
    # but still n<<sqrt(q) means q>>64. Use q in [2000,4000].
    cases=[]
    # n=8 (phi=4): (2r)^4 -- r=4 ->4096, r=5->10000, r=6->20736, r=7->38416
    for r,qlo in [(4,1000),(5,2000),(6,3000),(7,4000),(8,5000)]:
        q=find_prime_1modn(8,qlo)
        cases.append((8,q,r))
    # n=16 (phi=8): (2r)^8 huge; r=3 ->6^8=1.7e6 meets q~1e6
    for r,qlo in [(3,500000),(4,2000000)]:
        q=find_prime_1modn(16,qlo)
        cases.append((16,q,r))
    results=[]
    for (n,q,r) in cases:
        try:
            d=analyze(n,q,r); report(d); results.append(d)
        except Exception as ex:
            print(f"  n={n} q={q} r={r}: ERR {ex}")
    print("=== SUMMARY ===")
    print("identity anomaly==direct everywhere:", all(d['anomaly']==d['anomaly_direct'] for d in results))
    nz=[d for d in results if d['anomaly']>0]
    print(f"nonzero-anomaly cases: {len(nz)}/{len(results)}")
    for d in nz:
        print(f"  n={d['n']} q={d['q']} r={d['r']}: bound/E_Fp={d['bound']/d['Erp']:.2e}  (autocorr-cap bound is {'VACUOUS (>=E_Fp)' if d['bound']>=d['Erp'] else 'non-trivial'})")
