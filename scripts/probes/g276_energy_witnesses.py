#!/usr/bin/env python3
"""Exact-integer energy witnesses for G276 Lean certificate.

For each witness cell computes, as EXACT INTEGERS on Z_m = F_p^*/G:
  signed = m * sum_j wq_j rq_j - (sum wq)(sum rq)      (nonprincipal signed CORE gate)
  E_W    = m * sum_j wq_j^2   - (sum wq)^2              (nonprincipal L2 energy of W, >= 0)
  E_R    = m * sum_j rq_j^2   - (sum rq)^2              (nonprincipal L2 energy of R, >= 0)
Cauchy-Schwarz on the m-1 nonprincipal characters gives signed^2 <= E_W * E_R.
The slack ratio (E_W*E_R)/signed^2 is the exact-integer certificate that the signed
gate is a vanishing fraction of the geometric-mean pointwise (Weil-controllable) energy.
"""
from __future__ import annotations
from math import comb
import numpy as np


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def prime_factors(x):
    out=[]; d=2
    while d*d<=x:
        if x%d==0:
            out.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: out.append(x)
    return out

def primitive_root(p):
    fac=prime_factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    raise RuntimeError(p)

def subgroup(p,n):
    root=primitive_root(p); zeta=pow(root,(p-1)//n,p)
    G=[]; x=1
    for _ in range(n): G.append(x); x=x*zeta%p
    assert x==1 and len(set(G))==n
    return G, root

def profiles(p,n):
    G,root=subgroup(p,n)
    W=[0]*p
    for y in G:
        for z in G: W[(2*y-z)%p]+=1
    hist=[np.zeros(p,dtype=np.int64) for _ in range(7)]
    hist[0][0]=1
    for used,x in enumerate(G,1):
        for k in range(min(6,used),0,-1): hist[k]+=np.roll(hist[k-1],x)
    return W,hist,root

def corr(a,b,p):
    raw=np.fft.ifft(np.fft.fft(a)*np.conj(np.fft.fft(b))).real
    r=np.rint(raw); assert float(np.max(np.abs(raw-r)))<1e-3
    return [int(v) for v in r]

def cell(p,n,r):
    W,hist,root=profiles(p,n)
    R=corr(hist[r],hist[r-1],p)
    m=(p-1)//n
    SW=n*n; SR=comb(n,r)*comb(n,r-1)
    A=p*sum(W[x]*R[x] for x in range(p))-SW*SR
    wq=[p*W[pow(root,j,p)]-SW for j in range(m)]
    rq=[p*R[pow(root,j,p)]-SR for j in range(m)]
    assert (p*W[0]-SW)*(p*R[0]-SR)+n*sum(wq[j]*rq[j] for j in range(m))==p*A
    Swq=sum(wq); Srq=sum(rq)
    signed = m*sum(wq[j]*rq[j] for j in range(m)) - Swq*Srq
    E_W = m*sum(v*v for v in wq) - Swq*Swq
    E_R = m*sum(v*v for v in rq) - Srq*Srq
    assert E_W>=0 and E_R>=0
    assert signed*signed <= E_W*E_R, "Cauchy-Schwarz violated"
    return dict(p=p,n=n,r=r,m=m,A=A,signed=signed,E_W=E_W,E_R=E_R,
                slack=(E_W*E_R)//(signed*signed) if signed else None)

def main():
    ws=[(1153,16,5),(2081,16,5),(977,16,5),(2593,16,6),(70753,32,6)]
    for p,n,r in ws:
        assert is_prime(p) and (p-1)%n==0
        c=cell(p,n,r)
        print(f"n={c['n']} p={c['p']} r={c['r']} m={c['m']}")
        print(f"  A={c['A']}")
        print(f"  signed = {c['signed']}")
        print(f"  E_W    = {c['E_W']}")
        print(f"  E_R    = {c['E_R']}")
        print(f"  signed^2      = {c['signed']*c['signed']}")
        print(f"  E_W*E_R       = {c['E_W']*c['E_R']}")
        print(f"  slack floor   = (E_W*E_R)//signed^2 = {c['slack']}")
        print()

if __name__=="__main__":
    main()
