#!/usr/bin/env python3
"""Exact integer certificate for the strong-discordant BGK covariance witnesses.

Emits EXACT integers A_5, A_6, centeredW, centeredR_5, centeredR_6 for the
two strongly-anti-correlated primes so the Lean no-go can record verifiable
constants (no floats). Both A_5>0 and A_6<0 with both |rho| bounded away
from 0 -> refutes any single-rank sign reduction and any correlation-threshold
concordance gate.
"""
import math

def factor(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out
def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def subgroup(p,n):
    z=pow(primitive_root(p),(p-1)//n,p); G=[]; x=1
    for _ in range(n): G.append(x); x=x*z%p
    assert x==1 and len(set(G))==n
    return G
def subset_hist(G,p,r):
    # dp[k][t] via pure python ints
    dp=[[0]*p for _ in range(r+1)]; dp[0][0]=1; used=0
    for x in G:
        used+=1
        for k in range(min(r,used),0,-1):
            row=dp[k]; prev=dp[k-1]
            for t in range(p):
                v=prev[(t-x)%p]
                if v: row[t]+=v
    for k in range(r+1):
        assert sum(dp[k])==math.comb(len(G),k)
    return dp
def corr(a,b,p):
    c=[0]*p; nz=[(x,a[x]) for x in range(p) if a[x]]
    for t in range(p):
        s=0
        for x,av in nz:
            bv=b[(x-t)%p]
            if bv: s+=av*bv
        c[t]=s
    assert sum(c)==sum(a)*sum(b)
    return c
def cert(p,n,r):
    G=subgroup(p,n); dp=subset_hist(G,p,r)
    W=[0]*p
    for y in G:
        y2=(2*y)%p
        for z in G: W[(y2-z)%p]+=1
    assert sum(W)==n*n
    R=corr(dp[r],dp[r-1],p)
    totalR=math.comb(n,r)*math.comb(n,r-1)
    C12=sum(W[t]*R[t] for t in range(p))
    A=p*C12-n*n*totalR
    cW=p*sum(x*x for x in W)-n**4
    cR=p*sum(x*x for x in R)-totalR*totalR
    return A,cW,cR

for (p,n) in [(113,16),(257,32),(881,16),(89,8)]:
    A5,cW,cR5=cert(p,n,5)
    A6,_,cR6=cert(p,n,6)
    r5=A5/math.isqrt(cW*cR5)**1 if cW*cR5>0 else 0
    import math as m
    rho5=A5/m.sqrt(cW*cR5); rho6=A6/m.sqrt(cW*cR6)
    print(f"n={n} p={p}")
    print(f"  A5={A5}  A6={A6}   sign(A5)={'+' if A5>0 else '-'} sign(A6)={'+' if A6>0 else '-'}")
    print(f"  centeredW={cW}  centeredR5={cR5}  centeredR6={cR6}")
    print(f"  rho5={rho5:+.6f} rho6={rho6:+.6f}  A5*A6={A5*A6} (<0 => discordant)")
    print(f"  DISCORDANT={ (A5>0)!=(A6>0) }  both-strong-half={abs(rho5)>0.5 and abs(rho6)>0.5}  both-strong-fifth={abs(rho5)>0.2 and abs(rho6)>0.2}")
    print()
