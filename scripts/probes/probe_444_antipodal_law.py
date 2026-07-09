"""
probe_444_antipodal_law.py  (#444 -- the antipodal structure law of deep-band bad subsets)

probe_444_r4_descent found: bad subsets have antipodal-singletons = r-1 (sample). If ALL bad
subsets have a FIXED antipodal type (#pairs p, #singletons j with 2p+j=a0=r+1), that's a clean
structural law -> a route to the general-r census bound #bad <= K = 2^r*C(n/2,r).

Use LARGE prime (BabyBear 2013265921, char-0 worst case) to avoid char-p undercount. For r=3,4,5
at n=16: compute ALL bad subsets of the resonant line (x^{n/2}, x^{n/2-(2r-5)}), tabulate the
(#pairs,#singletons) distribution, and the distinct-gamma count + O_P. Check the law and ratio to K.
"""
import itertools
from math import comb, gcd
from collections import Counter

p = 2013265921  # BabyBear, 2^27 | p-1
def order_small(x):
    # only used to find generator; use multiplicative order via factoring p-1 is heavy, so
    # instead pick a known generator route: find w of order n directly.
    pass
def w_of_order(n):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1:
            return h
    raise RuntimeError("no w")

def band_gamma(pts, e, f, k, a0):
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

def antipodal_type(exps, n):
    Sset=set(exps); h=n//2
    pairs=sum(1 for j in exps if j<h and (j+h) in Sset)
    singles=sum(1 for j in exps if (j+h)%n not in Sset)
    return pairs, singles

def run(n, r):
    w=w_of_order(n); mu=[pow(w,i,p) for i in range(n)]
    e=n//2; f=n//2-(2*r-5); k=r-1; a0=r+1
    K=(1<<r)*comb(n//2,r); d=gcd((e-f)%n,n); mult=pow(w,(e-f)%n,p)
    types=Counter(); badset={}; zero_bad=False
    for Sidx in itertools.combinations(range(n),a0):
        pts=[mu[i] for i in Sidx]
        gv=band_gamma(pts,e,f,k,a0)
        if gv is None: continue
        if gv%p==0: zero_bad=True; continue
        t=antipodal_type(list(Sidx),n); types[t]+=1
        if gv not in badset: badset[gv]=Sidx
    nz=list(badset.keys())
    rem=set(nz); orbs=0
    while rem:
        x0=next(iter(rem)); cur=x0; o=set()
        for _ in range(n): o.add(cur); cur=cur*mult%p
        orbs+=1; rem-=o
    print(f"n={n} r={r} line(x^{e},x^{f}) a0={a0}: #bad(nz)={len(nz)}(+{int(zero_bad)} zero) "
          f"O_P={orbs} d={d} K={K} bad/K={len(nz)/K:.3f}")
    print(f"     antipodal (pairs,singles) distribution over bad subsets: {dict(types)}")
    # predicted law: all type (1, r-1)?  2*1+(r-1)=r+1=a0 ok
    pred=(1,r-1)
    only_pred = set(types.keys())=={pred} if types else False
    print(f"     law 'exactly (1,{r-1})' holds for ALL bad subsets: {only_pred}")
    return len(nz), orbs, K

for r in [3,4,5]:
    run(16, r)
print("--- n=32 spot checks (large prime, char-0) ---")
for r in [3,4]:
    run(32, r)
