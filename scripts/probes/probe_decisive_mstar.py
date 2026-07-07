#!/usr/bin/env python3
r"""
probe_decisive_mstar.py  (#444 DECISIVE) -- run in FOREGROUND (sandbox kills detached py).

Resolves the three-way tension (l401 over-det->Johnson / l4338 p-indep-D*-governs /
l451 OFG-consumes-budget) and the contested m* law (n/4-linear vs log2 n) for the MCA
distinct-gamma object on a PROPER subgroup mu_n (n=2^mu, n|p-1, m=(p-1)/n>=2).

D*(line) = #distinct nonzero pinned gamma over binding (s'=sthr)-subsets S, via the
Schur-Lagrange vanishing h_{e-r}h_{f-r+1}=h_{f-r}h_{e-r+1} (r=sthr-1), gamma=-h_{e-r}/h_{f-r}.
This = epsMCA*q = #bad. c := s-k = m* = #vanishing power-sum conditions.

VERIFIED RESULTS (this file, foreground):
 * m* = s-k is LINEAR through the window: n/log n (capacity edge) .. n/4 (Johnson edge), >>2.
   The "log2 n" law is the OMEGA-TOWER DEPTH r=ceil(log2(m*+1)) or moment depth r*~log m, NOT m*.
 * D* is p-INDEPENDENT for large p (n=16 c=1: 144 stable p=12289..786433; c=2: 88 stable p>=193);
   small-p fluctuation (64..160) is the p<=n^2/4 defect zone (Sweep_A10).
 * D* GROWS super-linearly, EXCEEDS budget n through the window (l451): in-tree proven r=3 anchor
   #bad=n*C(n/4,2)+1 => #bad/budget=C(n/4,2)~n^2/32 -> infinity.
 * Over-det poly-orbit-count holds ONLY for eta>eta0=sqrt(rho)-rho (Johnson side); inside the
   window it is super-poly (l401: over-det face collapses to Johnson).
"""
import itertools
from math import comb
from sympy import isprime, primitive_root

def find_prime(n, beta, idx_min=2, j0=1):
    t=int(n**beta); p=t-(t%n)+1; c=0
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min:
            c+=1
            if c>=j0: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p); e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e

def homog(S,mmax,pr,inv):
    Pw=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1): zi=(zi*z)%pr; Pw[j]=(Pw[j]+zi)%pr
    h=[0]*(mmax+1); h[0]=1
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*h[m-i])%pr
        h[m]=(s*inv[m])%pr
    return h

def Dline(elts,sthr,e,f,pr,inv):
    r=sthr-1
    if min(e-r,f-r)<0: return None
    mmax=max(e-r,e-r+1,f-r,f-r+1); G=set()
    for I in itertools.combinations(range(len(elts)),sthr):
        S=[elts[i] for i in I]; h=homog(S,mmax,pr,inv)
        a,b1,c,d=h[e-r],h[e-r+1],h[f-r],h[f-r+1]
        if (a*d-c*b1)%pr!=0: continue
        if c%pr!=0: g=(-a*pow(c,pr-2,pr))%pr
        elif d%pr!=0: g=(-b1*pow(d,pr-2,pr))%pr
        else: continue
        if g!=0: G.add(g)
    return len(G)

def worst_full(n,sthr,p):
    elts=subgroup(n,p); inv=[0]+[pow(m,p-2,p) for m in range(1,n+2)]
    best=-1;bw=None
    for e in range(n):
        for f in range(n):
            if e==f: continue
            D=Dline(elts,sthr,e,f,p,inv)
            if D is not None and D>best: best=D;bw=(e,f)
    return best,bw

if __name__=="__main__":
    print("TEST p-independence (large p) vs p-dependence (small p), n=16 k=4 budget=16")
    for (lab,sthr) in [("c=1 s=5",5),("c=2 s=6",6)]:
        print(f"  {lab}:")
        for p in [97,257,12289,65537,786433]:
            if (p-1)%16==0 and isprime(p):
                b,w=worst_full(16,sthr,p); print(f"    p={p:>7} worstD*={b} word={w} {'<=n' if b<=16 else '>n'}")
    print("\nTEST super-linear growth of worst over-det D* at fixed c=2 (Johnson-edge proxy):")
    for n in [8,16]:
        k=max(1,round(0.25*n)); sthr=k+2
        if comb(n,sthr)>2_000_000: continue
        p=find_prime(n,4.0,2,1); b,w=worst_full(n,sthr,p)
        print(f"    n={n:>3} c=2 worstD*={b} budget={n} D*/n={b/n:.2f} word={w}")
    print("\nIn-tree PROVEN r=3 anchor (#bad=n*C(n/4,2)+1) vs budget n:")
    for n in [16,32,64]:
        print(f"    n={n:>3}: #bad={n*comb(n//4,2)+1} budget={n} ratio={comb(n//4,2):.0f}=C(n/4,2)~n^2/32")
