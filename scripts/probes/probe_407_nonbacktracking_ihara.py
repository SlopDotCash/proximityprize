#!/usr/bin/env python3
import math, numpy as np, sys

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def odd_part(x):
    while x%2==0: x//=2
    return x

def primitive_root(p):
    phi=p-1; facs=[]; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            facs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: facs.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def find_prime(n, beta, used, pmax):
    target=int(round(n**beta))
    p=target-(target%n)+1
    for _ in range(2000000):
        if p>pmax: return None
        if p>3 and is_prime(p) and odd_part((p-1)//n)>1 and p not in used:
            used.add(p); return p
        p+=n
    return None

def all_periods(p, n):
    g=primitive_root(p); eta=pow(g,(p-1)//n,p)
    xs=np.array([pow(eta,i,p) for i in range(n)], dtype=np.int64)
    bs=np.arange(1,p,dtype=np.int64); twp=2.0*math.pi/p
    out=np.empty(p-1, dtype=np.complex128)
    CH=max(1, 6_000_000//n)
    for s in range(0,p-1,CH):
        e=min(s+CH,p-1); blk=bs[s:e]
        ang=((blk[:,None]*xs[None,:])%p).astype(np.float64)*twp
        out[s:e]=np.cos(ang).sum(1)+1j*np.sin(ang).sum(1)
    return out

def main():
    print("="*104, flush=True)
    print(" #407 NON-BACKTRACKING / IHARA-BASS ROUTE  (B vs Ramanujan 2sqrt(n-1); nb-spectral-radius)", flush=True)
    print("="*104, flush=True)
    used=set()
    PMAX=22_000_000
    print(f"\n{'n':>5}{'beta':>5}{'p':>11}{'m':>8}{'B':>9}{'sqrt(n)':>8}{'B/sqn':>7}"
          f"{'2sq(n-1)':>9}{'B/2sq':>7}{'rho_nb':>8}{'sq(n-1)':>8}{'rho/sq':>7}{'#>2sq':>7}", flush=True)
    for mu in (4,5,6):
        n=1<<mu
        for beta in (3.5,4.0,4.5):
            p=find_prime(n,beta,used,PMAX)
            if p is None: 
                print(f"{n:>5}{beta:>5.1f}   (no prime <= {PMAX})", flush=True); continue
            m=(p-1)//n
            eta=all_periods(p,n)
            absn=np.abs(eta)
            mask=absn < n-1e-6
            B=float(absn[mask].max())
            lam=eta.real
            imag_max=float(np.abs(eta.imag).max())
            disc=lam.astype(np.complex128)**2 - 4*(n-1)
            mu1=(lam+np.sqrt(disc))/2; mu2=(lam-np.sqrt(disc))/2
            rho_nb=float(max(np.abs(mu1[mask]).max(), np.abs(mu2[mask]).max()))
            sq=math.sqrt(n-1); sqn=math.sqrt(n)
            n_outlier=int(np.sum(np.abs(lam[mask])>2*sq))  # eigenvalues outside Ramanujan window
            print(f"{n:>5}{beta:>5.1f}{p:>11}{m:>8}{B:>9.2f}{sqn:>8.2f}{B/sqn:>7.2f}"
                  f"{2*sq:>9.2f}{B/(2*sq):>7.2f}{rho_nb:>8.2f}{sq:>8.2f}{rho_nb/sq:>7.2f}{n_outlier:>7}"
                  f"  (im<{imag_max:.0e})", flush=True)

if __name__=="__main__":
    main()
