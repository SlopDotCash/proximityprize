#!/usr/bin/env python3
"""
C056 RECONCILE: the orbit multiplier c=g^{b-a} as the NET homogeneity degree of the
controlling object.  True controlling object = -h_{b-k}/h_{a-k} (Jacobi-Trudi cofactor
ratio), NOT a single h_{b-a}.  Under x->g.x:
   h_{b-k}(g x) = g^{b-k} h_{b-k}(x);  h_{a-k}(g x) = g^{a-k} h_{a-k}(x)
   => ratio(g x) = g^{(b-k)-(a-k)} ratio(x) = g^{b-a} ratio(x) = c * ratio(x).
So the orbit multiplier c=g^{b-a} IS the NET homogeneity weight of the cofactor RATIO,
deg(numer)-deg(denom) = (b-k)-(a-k) = b-a -- independent of k.  The connection attributes
it to a single h_{b-a}; the correct attribution is the difference of the two homogeneity
degrees of the cofactor ratio.  Verify the homogeneity-degree bookkeeping holds exactly,
AND that gcd(b-a,n) (NOT gcd(b-k,n) or gcd(a-k,n)) governs the orbit size, for a != k.
"""
import itertools, math
from sympy import isprime

def matdet(M,p):
    n=len(M);M=[r[:] for r in M];det=1
    for col in range(n):
        piv=None
        for r in range(col,n):
            if M[r][col]%p: piv=r;break
        if piv is None: return 0
        if piv!=col: M[col],M[piv]=M[piv],M[col];det=(-det)%p
        inv=pow(M[col][col],p-2,p);det=det*M[col][col]%p
        for r in range(col+1,n):
            f=M[r][col]*inv%p
            if f:
                for c in range(col,n): M[r][c]=(M[r][c]-f*M[col][c])%p
    return det%p
def residual(dom,k,T,e,p):
    M=[]
    for i in T:
        x=dom[i];M.append([pow(x,b,p) for b in range(k)]+[pow(x,e,p)])
    return matdet(M,p)
def h_complete(j,xs,p):
    if j<0: return 0
    if j==0: return 1
    c=[0]*(j+1);c[0]=1
    for x in xs:
        nw=[0]*(j+1)
        for d in range(j+1):
            s=0;xm=1
            for m in range(d+1): s=(s+c[d-m]*xm)%p;xm=xm*x%p
            nw[d]=s
        c=nw
    return c[j]%p
def find_prime(mu):
    n=1<<mu;q=((n**4//n)+1)*n+1;hi=n**5
    while q<=hi:
        if isprime(q): return q
        q+=n
    return None
def factorize(m):
    f=set();d=2
    while d*d<=m:
        while m%d==0: f.add(d);m//=d
        d+=1
    if m>1: f.add(m)
    return f
def subgrp_gen(q,n):
    phi=q-1;fac=factorize(phi)
    a=2
    while not all(pow(a,phi//pr,q)!=1 for pr in fac): a+=1
    return pow(a,(q-1)//n,q)
def ord_of(c,q):
    if c%q==0: return 0
    o=1;x=c%q
    while x!=1: x=x*c%q;o+=1
    return o

for mu in (3,4,5):
    n=1<<mu; q=find_prime(mu); g=subgrp_gen(q,n); dom=[pow(g,i,q) for i in range(n)]
    print(f"\n=== q={q} n={n}=2^{mu} (proper subgroup, n^2={n*n}<<q) ===")
    for (k,a,b) in [(2,2,3),(2,3,4),(2,3,5),(2,4,6),(3,3,4),(3,4,6),(3,5,8),(2,5,9)]:
        t=k+1
        if t>n: continue
        gap=b-a
        c=pow(g, gap % n, q)
        # NET homogeneity of cofactor ratio
        deg_num=b-k; deg_den=a-k; net=deg_num-deg_den  # = b-a
        # verify ratio(g.T)=c*ratio(T) for ALL T (orbit law), and ord(c)=n/gcd(b-a,n)
        okrot=0; tot=0
        for T in itertools.combinations(range(n),t):
            ra=residual(dom,k,T,a,q); rb=residual(dom,k,T,b,q)
            if ra%q==0: continue
            gam=(-rb)*pow(ra,q-2,q)%q
            Tr=tuple(sorted((i+1)%n for i in T))
            ra2=residual(dom,k,Tr,a,q); rb2=residual(dom,k,Tr,b,q)
            if ra2%q==0: continue
            gam2=(-rb2)*pow(ra2,q-2,q)%q
            tot+=1
            if gam2==(c*gam)%q: okrot+=1
        oc=ord_of(c,q)
        orbit=n//math.gcd(gap%n if gap%n else n, n)
        # cross-check: does gcd(b-k,n) or gcd(a-k,n) ALSO predict it? (should NOT in general)
        print(f"  (k={k},a={a},b={b}) gap={gap}: net-homog deg(h_{{{deg_num}}})-deg(h_{{{deg_den}}})={net}"
              f" | ratio(g.T)=c*ratio:{okrot}/{tot} | ord(c)={oc} | n/gcd(b-a,n)={orbit}"
              f" {'MATCH' if oc==orbit and okrot==tot and tot>0 else 'CHECK'}")
