"""
probe_444_angleC_coset.py -- Angle C: characterize the bad-gamma orbit REPRESENTATIVES.

Since gamma(gS)=g^{e-f}gamma(S), the nonzero gammas form a union of orbits under mult-by-g^{e-f}.
When d=gcd(e-f,n)=1, <g^{e-f}>=mu_n, so each orbit is a full coset of mu_n in F_p^*, of size n.
O_P = #distinct cosets gamma*mu_n that contain a bad gamma.

KEY question for a crude O_P bound: can we identify a SINGLE algebraic invariant J(S), defined on
mu_n-orbits of S, such that
   (a) J is dilation-INVARIANT (constant on each gamma-orbit), and
   (b) gamma is a function of J (so distinct gammas <-> distinct J), and
   (c) J ranges over a set of provably-bounded size <= K*d/n.

Natural candidates for J (dilation-weight-0 combos):
   - the coset gamma*mu_n itself (i.e. gamma^n in the quotient) -- tautological
   - ratios of symmetric functions h_a^b/h_c^d with weight a*b - c*d = 0
   - the "shape" of S = multiset of gaps / the orbit of S under dilation

We compute gamma^n (= coset invariant in F_p^* / mu_n, since (g^{e-f}gamma)^n=gamma^n as g^n=1)
and check: is gamma -> gamma^n INJECTIVE on orbits? i.e. is O_P = #distinct gamma^n values?
If yes, O_P = #distinct gamma^n = #distinct values of an explicit symmetric-rational function of
degree n*(weight) -> Bezout/degree bound gives O_P bound.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
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
    if (her*hfr1-hfr*her1)%p!=0: return None
    if hfr==0: return ('zero' if her==0 else 'inf',)
    g=(-her*pow(hfr,p-2,p))%p
    return ('val',g) if g!=0 else ('zero',)

def study(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); mult=pow(w,(e-f)%n,p)
    nz=set()
    for Sidx in combinations(range(n),a0):
        res=badgamma(Sidx,w,e,f,r,p)
        if res and res[0]=='val': nz.add(res[1])
    # orbit count
    rem=set(nz); OP=0
    while rem:
        x=next(iter(rem)); cur=x
        for _ in range(n): rem.discard(cur); cur=cur*mult%p
        OP+=1
    # coset invariant: gamma^(n/d) is invariant under mult-by-g^{e-f}? check.
    # mult = g^{e-f}, mult^(n/d)=g^{(e-f)n/d}=1 iff (e-f)*n/d == 0 mod n iff (e-f)/d *n ==0 mod n: yes since (e-f)/d integer. So gamma^{n/d} invariant.
    nd=n//d
    cosets=set((pow(g,nd,p)) for g in nz)
    # is gamma->gamma^{n/d} injective on orbits? i.e. #distinct gamma^{n/d} == O_P?
    inj = (len(cosets)==OP)
    K=(1<<r)*comb(n//2,r)
    print(f"r={r} n={n} (x^{e},x^{f}) d={d} nd={nd}: O_P={OP} K*d/n={K*d/n:.1f}  "
          f"#distinct gamma^(n/d)={len(cosets)} coset-inj?={inj}  O_P<=Kd/n?={OP<=K*d/n}")
    return OP,inj

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1),
           6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(3,32),(4,32),(5,16)]
    if len(sys.argv)>1:
        todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
