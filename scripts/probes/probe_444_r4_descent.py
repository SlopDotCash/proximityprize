"""
probe_444_r4_descent.py  (#444 -- attack the OPEN r=4 demand-side via odd-descent)

The deep-band demand-side census-domination is OPEN for general r (r=3 closed:
#bad=n*C(n/4,2)+1). r=4 resonant line (campaign): x^{n/2}+g*x^{n/2-3} = x^{n/2-3}(x^3+g),
the CUBE analogue of my binding x^{n/2-1}(x^2+g) [r=3]. Deep band: a0=r+1=5, k=r-1=3.

Apply the level-set / odd-descent tool:
  agreement f(x)=x^{n/2-3}(x^3+g) on S, deg f<3
  => x^3+g = f(x)*x^{3-n/2} = f(x)*x^3*chi(x)  (chi=x^{n/2}, x^{-n/2}=chi on mu_n)
  => psi_f(x) := f(x)*x^3*chi(x) - x^3 = g  constant on S.
Check: (1) #bad gamma at n=16,32,(64); compare to K=2^4*C(n/2,4); (2) the support/parity of
psi_f-gamma (does it descend like r=3?); (3) the bad-subset antipodal structure; (4) O_P orbit
count + try a closed form.
"""
import itertools
from math import comb
from collections import Counter

def order(x,p):
    o,cur=1,x
    while cur!=1: cur=cur*x%p; o+=1
    return o

def setup(n,p):
    g=2
    while order(g,p)!=p-1: g+=1
    w=pow(g,(p-1)//n,p)
    return w,[pow(w,i,p) for i in range(n)]

def band_gamma(S, e, f, k, a0, p):
    """line x^e+gamma x^f; interpolate both on S (|S|=a0); gamma consistent making deg<k? return gamma or None."""
    pts=list(S)
    m=len(pts)
    def interp(vals):
        A=[[pow(pts[i],j,p) for j in range(m)] for i in range(m)]
        M=[A[i][:]+[vals[i]%p] for i in range(m)]
        for col in range(m):
            piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
            if piv is None: return None
            M[col],M[piv]=M[piv],M[col]
            inv=pow(M[col][col],p-2,p); M[col]=[(v*inv)%p for v in M[col]]
            for rr in range(m):
                if rr!=col and M[rr][col]%p!=0:
                    c=M[rr][col]; M[rr]=[(M[rr][t]-c*M[col][t])%p for t in range(m+1)]
        return [M[i][m]%p for i in range(m)]
    c0=interp([pow(t,e,p) for t in pts]); c1=interp([pow(t,f,p) for t in pts])
    if c0 is None or c1 is None: return None
    gam=None; nd=False
    for j in range(k,a0):
        x0=c0[j]; x1=c1[j]
        if x0 or x1: nd=True
        if x1==0:
            if x0: return None
        else:
            g_=(-x0*pow(x1,p-2,p))%p
            if gam is None: gam=g_
            elif gam!=g_: return None
    return gam if nd else None

def run(n, p, r):
    w,mu=setup(n,p)
    e,f=n//2, n//2-(2*r-5)   # r=3:gap1 (n/2-1); r=4:gap3 (n/2-3); matches resonant adjacents
    # actually use the campaign resonant gap: r=3 -> f=n/2-1; r=4 -> f=n/2-3
    f = n//2 - (2*r-5)
    k=r-1; a0=r+1
    K=(1<<r)*comb(n//2,r)
    mult=pow(w,(e-f)%n,p)  # dilation factor g^{e-f}
    badset={}
    for S in itertools.combinations(mu,a0):
        gv=band_gamma(S,e,f,k,a0,p)
        if gv is None: continue
        if gv%p!=0 and gv not in badset: badset[gv]=S
    nz=list(badset.keys())
    has0 = any(band_gamma(S,e,f,k,a0,p)==0 for S in [])  # skip; track via separate
    # O_P
    d=__import__('math').gcd((e-f)%n,n)
    rem=set(nz); orbs=0
    while rem:
        x0=next(iter(rem)); cur=x0; o=set()
        for _ in range(n):
            o.add(cur); cur=cur*mult%p
        orbs+=1; rem-=o
    # antipodal structure of one bad subset (exponents base w; check singleton/pair split)
    sample=None
    if nz:
        S=badset[nz[0]]; exps=sorted(mu.index(x) for x in S)
        # count antipodal singletons (j s.t. j+n/2 not in S)
        Sset=set(exps); singles=[j for j in exps if (j+n//2)%n not in Sset]
        sample=(exps, len(singles))
    print(f"n={n} r={r} line(x^{e},x^{f}) a0={a0} k={k}: #bad(nz)={len(nz)} O_P={orbs} d={d} "
          f"(n/d)*O_P+?={ (n//d)*orbs } K={K} bad<=K:{len(nz)<=K}")
    if sample: print(f"      sample bad subset exps={sample[0]} antipodal-singletons={sample[1]}")
    return len(nz), orbs, K

print("=== r=3 calibration (should reproduce n*C(n/4,2)+1) ===")
run(16, 65537, 3); run(32, 65537, 3)
print("=== r=4 (OPEN) via the cube-line descent ===")
run(16, 65537, 4)
run(32, 65537, 4)
