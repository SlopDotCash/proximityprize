"""
probe_444_mech1_sameparity_descent.py -- MECHANISM-1 (same-parity => antipodal => mu_{n/2} descent).

Goal: for SAME-PARITY lines (e==f mod 2), test rigorously the chain
  (i)   W_gamma(-x) = (-1)^e W_gamma(x)   [trivial: monomials x^e,x^f same parity]
  (ii)  the bad condition V (Schur 2x2 vanishing in h_{e-r},h_{f-r},...) reorganizes under x->-x
  (iii) for the MAXIMIZER same-parity line, J=gamma^{n/d} is a function of (r-1)-data inside
        mu_{n/2}=squares, with image size <= C(n/2,r-1).

CORE OBSERVATION to test:
  Under x->-x (x->w^{n/2} x), the power sums P_i(S)=sum_{s in S} s^i transform as
     P_i(-S) = (-1)^i P_i(S).
  Hence h_m(S) is NOT simply (-1)^m h_m(S) unless S is antipodally symmetric.
  But the BAD VARIETY is dilation-invariant; the antipode x->-x is the dilation by w^{n/2}.
  So V is preserved by S -> w^{n/2} S, and gamma(w^{n/2} S) = (w^{n/2})^{e-f} gamma(S)
     = (-1)^{e-f} gamma(S) = gamma(S)  since e-f even (same parity).
  => The antipodal map acts on the gamma-VALUE with eigenvalue (-1)^{e-f}=+1 for same parity.
  This is the structural reason same-parity is special: antipode FIXES gamma (not just scales it).

We test:
  (A) confirm gamma(w^{n/2} S) = (-1)^{e-f} gamma(S) exactly (so for same-parity gamma is antipode-FIXED).
  (B) since J=gamma^{n/d} and d=gcd(e-f,n): for same-parity e-f is even so 2 | (e-f), thus
      d is even, n/d <= n/2.  Test that the distinct-J map factors through mu_{n/2}.
  (C) Antipodal type distribution of bad subsets ON the same-parity maximizer line specifically.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]

def gen(n,p):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def gamma_of(Sidx,w,e,f,r,p):
    Spts=[pow(w,i,p) for i in Sidx]
    M=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return None
    H=hpow(Spts,M,p)
    her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
    if (her*hfr1-hfr*her1)%p: return None
    if hfr==0: return ('inf',) if her else ('deg',)
    g=(-her*pow(hfr,p-2,p))%p
    return ('zero',) if g==0 else ('val',g)

def find_sameparity_maximizer(n,r,p):
    """scan all same-parity lines, return the one with max O_P."""
    w=gen(n,p); a0=r+1
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n,p) for S in subs]
    best=(0,None,0)
    for e in range(r,n):
        for f in range(r,n):
            if e==f or (e-f)%2!=0: continue   # same parity
            if max(e-r+1,f-r+1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d; cos=set()
            for H in Hc:
                if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
                if H[f-r]==0: continue
                g=(-H[e-r]*pow(H[f-r],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            if len(cos)>best[0]: best=(len(cos),(e,f),d)
    return w,best

def antipode_test(n,r,e,f,w,p):
    """(A) verify gamma(w^{n/2} S)=(-1)^{e-f} gamma(S);  (C) antipodal type of bad subsets."""
    half=n//2
    types=Counter(); fixchk=0; fixtot=0; nz=set(); d=gcd((e-f)%n,n); nd=n//d
    Sset_all=list(combinations(range(n),r+1))
    for Sidx in Sset_all:
        res=gamma_of(Sidx,w,e,f,r,p)
        if res is None or res[0] in ('inf','deg','zero'): continue
        g=res[1]; nz.add(pow(g,nd,p))
        # antipode of S: shift each index by half (mod n) -- this is multiply pts by w^{half}=-1
        Santi=tuple(sorted((i+half)%n for i in Sidx))
        res2=gamma_of(Santi,w,e,f,r,p)
        if res2 is not None and res2[0]=='val':
            fixtot+=1
            sign=(-1)**((e-f))   # = +1 for same parity
            if res2[1]==(sign*g)%p: fixchk+=1
        # antipodal type
        Si=set(Sidx); pairs=sum(1 for j in Sidx if j<half and (j+half) in Si)
        singles=(r+1)-2*pairs
        types[(pairs,singles)]+=1
    return len(nz),dict(types),fixchk,fixtot

if __name__=="__main__":
    todo=[(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    p=PRIMES[0]
    for (r,n) in todo:
        w,(opmax,line,d)=find_sameparity_maximizer(n,r,p)
        e,f=line
        nzJ,types,fixchk,fixtot=antipode_test(n,r,e,f,w,p)
        print(f"r={r} n={n}: SAME-PARITY maximizer line=(x^{e},x^{f}) [e-f={e-f} even], O_P={opmax}, d={d}")
        print(f"    C(n/2,r-1)={comb(n//2,r-1)}  O_P/bound={opmax/comb(n//2,r-1):.3f}")
        print(f"    (A) gamma(antipode S)=(-1)^(e-f) gamma(S): {fixchk}/{fixtot} (should be all)")
        print(f"    (C) antipodal-type (pairs,singles) of bad subsets: {types}")
