#!/usr/bin/env python3
"""Exact finite probe for the BGK late-transition alignment A_r.

W(t) = #{(y,z) in G^2 : 2y-z=t}
R_r(t) = #{(A,B): A subset G, |A|=r, B subset G, |B|=r-1, sum(A)-sum(B)=t}
A_r = p*sum_t W(t)R_r(t) - n^2*C(n,r)*C(n,r-1).

Subset histograms and W are exact integers. Circular correlation uses FFT and is
accepted only after integral rounding and exact mass/nonnegativity checks; small
cells are also checked against quadratic correlation.
"""
from __future__ import annotations
import math
import numpy as np


def factor(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out

def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise ValueError(p)

def subgroup(p,n):
    assert (p-1)%n==0
    z=pow(primitive_root(p),(p-1)//n,p)
    G=[]; x=1
    for _ in range(n): G.append(x); x=x*z%p
    assert x==1 and len(set(G))==n
    return G

def subset_hists(G,p,R):
    dp=np.zeros((R+1,p),dtype=np.int64); dp[0,0]=1
    used=0
    for x in G:
        used+=1
        for k in range(min(R,used),0,-1):
            dp[k] += np.roll(dp[k-1],x)
    for k in range(R+1):
        assert int(dp[k].sum())==math.comb(len(G),k)
    return dp

def circ_corr(a,b):
    # c[t] = sum_x a[x] b[x-t]
    c=np.rint(np.fft.ifft(np.fft.fft(a)*np.conj(np.fft.fft(b))).real).astype(np.int64)
    assert c.min()>=0
    assert int(c.sum())==int(a.sum())*int(b.sum())
    if len(a)<=300:
        brute=np.array([sum(int(a[x])*int(b[(x-t)%len(a)]) for x in range(len(a))) for t in range(len(a))],dtype=np.int64)
        assert np.array_equal(c,brute), (c,brute)
    return c

def row(n,p,r):
    G=subgroup(p,n); dp=subset_hists(G,p,r)
    W=np.zeros(p,dtype=np.int64)
    GS=set(G)
    for y in G:
        for z in G: W[(2*y-z)%p]+=1
    assert int(W.sum())==n*n
    assert all(int(W[t])==sum(1 for y in G if (2*y-t)%p in GS) for t in range(p))
    R=circ_corr(dp[r],dp[r-1])
    totalR=math.comb(n,r)*math.comb(n,r-1)
    C12=sum(int(W[t])*int(R[t]) for t in range(p))
    baseline=n*n*totalR
    A=p*C12-baseline
    ratio=p*C12/baseline
    centeredW=p*sum(int(x)*int(x) for x in W)-n**4
    centeredR=p*sum(int(x)*int(x) for x in R)-totalR**2
    rho=A/math.sqrt(centeredW*centeredR) if centeredW and centeredR else 0.0
    top=sorted(range(p),key=lambda t:int(W[t])*int(R[t]),reverse=True)[:5]
    return dict(n=n,p=p,v2=((p-1)&-(p-1)).bit_length()-1,r=r,A=A,ratio=ratio,rho=rho,
                C12=C12,totalR=totalR,maxW=int(W.max()),maxR=int(R.max()),
                W0=int(W[0]),R0=int(R[0]),topWR=[(t,int(W[t]),int(R[t])) for t in top])

def main():
    cells=[(8,17),(8,41),(8,73),(8,97),(8,257),
           (16,17),(16,97),(16,193),(16,257),(16,401),(16,769),(16,65537),
           (32,97),(32,193),(32,257),(32,353),(32,449),(32,577),(32,769),(32,65537)]
    print(' n      p v2 r sign      ratio-1          rho    W0 maxW       R0   maxR top(t,W,R)')
    for n,p in cells:
        for r in (5,6):
            if r>n: continue
            d=row(n,p,r)
            print(f"{n:2d} {p:6d} {d['v2']:2d} {r} {('+' if d['A']>0 else '-' if d['A']<0 else '0'):>4s} "
                  f"{d['ratio']-1:+.9e} {d['rho']:+.6f} {d['W0']:4d} {d['maxW']:4d} "
                  f"{d['R0']:8d} {d['maxR']:7d} {d['topWR'][:2]}")

if __name__=='__main__': main()
