"""
probe_444_angleC_structure.py -- Angle C structural deep-dive (FAST, n<=32 r<=4 exact).

Goal: understand the ALGEBRAIC STRUCTURE of the nonzero-gamma VALUE SET, to bound O_P directly.

For each bad S we record gamma AND e_1(S)=sum g^i (Vieta-style invariant) AND the multiset of
indices.  We test:
  (H1) gamma == -e_1(S) * (some fixed unit)?  (r=3: gamma=-e_1 exactly.)
  (H2) gamma orbits = cosets of a fixed cyclic subgroup of F_p* ?  (orbit = {gamma*g^{(e-f)t}})
  (H3) Each gamma is determined by a SMALLER invariant: gamma=poly in a bounded # of "free"
       symmetric coordinates -> O_P <= (count of those) -> the crude bound.
  (H4) The bad-S set is a union of dilation-orbits whose REPRESENTATIVES are indexed by a
       bounded-degree variety -> O_P bound.

Also: directly list the gamma VALUES per orbit-rep and see if they lie in a small algebraic set.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P = 2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1):
        Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def badgamma(Sidx,w,e,f,r,p=P):
    Spts=[pow(w,i,p) for i in Sidx]
    M=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return None
    H=hpow(Spts,M,p)
    her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
    det=(her*hfr1-hfr*her1)%p
    if det!=0: return None
    if hfr==0: return ('zero' if her==0 else 'inf',)
    g=(-her*pow(hfr,p-2,p))%p
    return ('val',g) if g!=0 else ('zero',)

def study(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1
    d=gcd((e-f)%n,n); mult=pow(w,(e-f)%n,p)
    # collect: gamma -> list of S (as sorted tuples); also e1, e_{a0} etc per S
    g2S=defaultdict(list)
    zero=False; inf=0
    for Sidx in combinations(range(n),a0):
        res=badgamma(Sidx,w,e,f,r,p)
        if res is None: continue
        if res[0]=='zero': zero=True; continue
        if res[0]=='inf': inf+=1; continue
        g2S[res[1]].append(Sidx)
    nz=set(g2S.keys())
    # orbit decomp
    rem=set(nz); orbreps=[]
    while rem:
        x=next(iter(rem)); o=set(); cur=x
        for _ in range(n): o.add(cur); cur=cur*mult%p
        orbreps.append(min(o&nz)); rem-=(o&nz); rem-=o
    OP=len(orbreps)
    K=(1<<r)*comb(n//2,r); Kdn=K*d//gcd(K*d,n)  # not exact div; use float
    # H1: gamma == -e1(S)*unit ? test the ratio gamma/e1(S) constant
    ratios=set()
    for g,Ss in list(g2S.items())[:200]:
        S=Ss[0]; e1=sum(pow(w,i,p) for i in S)%p
        if e1: ratios.add((g*pow(e1,p-2,p))%p)
    # H1b: gamma == -(some elementary symm e_j(S))? test which single e_j(S) (over all S for a g)
    # compute for each gamma whether gamma is -e_1, -e_{a0}, etc (most common single invariant)
    print(f"--- r={r} n={n} line(x^{e},x^{f}) d={d} ---")
    print(f"  O_P={OP}  #bad(nz)={len(nz)}  zero={zero}  inf-pins={inf}  K={K}  K*d/n={K*d/n:.2f}  O_P<=Kd/n? {OP<=K*d/n}")
    print(f"  orbit sizes: {Counter(len(set(_orbit(g,mult,nz,n))) for g in orbreps)}")
    print(f"  H1 gamma/e1(S) distinct ratios (<=5 shown): {sorted(ratios)[:5]} (#={len(ratios)})")
    # H3: how many distinct e1(S) values across bad S? and across orbit reps?
    e1vals=set()
    for g,Ss in g2S.items():
        for S in Ss: e1vals.add(sum(pow(w,i,p) for i in S)%p)
    print(f"  #distinct e1(S) over all bad S = {len(e1vals)}")
    return OP,K,d,n

def _orbit(g,mult,nz,n,p=P):
    o=set(); cur=g
    for _ in range(n): o.add(cur); cur=cur*mult%p
    return o&nz

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1)}
    todo=[(3,16),(4,16),(3,32),(4,32)]
    if len(sys.argv)>1:
        todo=[]
        for a in sys.argv[1:]:
            r,n=map(int,a.split(':')); todo.append((r,n))
    for (r,n) in todo:
        e,f=LINES[r](n)
        study(n,r,e,f)
