#!/usr/bin/env python3
"""
C056 SHARPEN: pin EXACTLY when "residual ratio = -h_{b-a}(x_T)" holds.

Hypothesis from first probe: ratio == -h_{b-a} holds when a == k (denominator residual
of x^a = x^k is the plain Vandermonde, ratio = -reducedcoeff_b[k] = -h_{b-k}).  But the
connection states it for "general monomial gap (a,b)".  Test a != k (a > k, since a < k
gives a degenerate zero denominator), e.g. a=k+1, and see if -h_{b-a} still equals ratio,
or whether the true controlling object is the QUOTIENT of two reduced coeffs (Jacobi-Trudi
cofactor ratio) -- a RATIO of complete-homogeneous polys, NOT a single h_{b-a}.
"""
import itertools, math
from sympy import isprime

def matdet(M, p):
    n=len(M); M=[r[:] for r in M]; det=1
    for col in range(n):
        piv=None
        for r in range(col,n):
            if M[r][col]%p: piv=r;break
        if piv is None: return 0
        if piv!=col: M[col],M[piv]=M[piv],M[col]; det=(-det)%p
        inv=pow(M[col][col],p-2,p); det=det*M[col][col]%p
        for r in range(col+1,n):
            f=M[r][col]*inv%p
            if f:
                for c in range(col,n): M[r][c]=(M[r][c]-f*M[col][c])%p
    return det%p

def residual(dom,k,T,expo,p):
    M=[]
    for i in T:
        x=dom[i]; M.append([pow(x,b,p) for b in range(k)]+[pow(x,expo,p)])
    return matdet(M,p)

def poly_mod_coreVanish(b,roots,p):
    t=len(roots); poly=[1]
    for x in roots:
        new=[0]*(len(poly)+1)
        for j in range(len(poly)):
            new[j]=(new[j]-x*poly[j])%p; new[j+1]=(new[j+1]+poly[j])%p
        poly=new
    rem=[0]*(b+1); rem[b]=1; cv=poly
    for deg in range(b,t-1,-1):
        if deg<len(rem) and rem[deg]%p:
            coef=rem[deg]
            for j in range(len(cv)): rem[deg-t+j]=(rem[deg-t+j]-coef*cv[j])%p
    return [c%p for c in rem[:t]]

def h_complete(j,xs,p):
    if j==0: return 1
    if j<0: return 0
    coeffs=[0]*(j+1); coeffs[0]=1
    for x in xs:
        new=[0]*(j+1)
        for d in range(j+1):
            s=0;xm=1
            for m in range(d+1):
                s=(s+coeffs[d-m]*xm)%p; xm=xm*x%p
            new[d]=s
        coeffs=new
    return coeffs[j]%p

def find_prime(mu):
    n=1<<mu; lo=n**4; q=((lo//n)+1)*n+1; hi=n**5
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
    def isg(a): return all(pow(a,phi//pr,q)!=1 for pr in fac)
    a=2
    while not isg(a): a+=1
    return pow(a,(q-1)//n,q)

q=find_prime(4); n=16; g=subgrp_gen(q,n); dom=[pow(g,i,q) for i in range(n)]
print(f"q={q}, n={n}, g order={n}")
print("Testing ratio == -h_{b-a} for a != k (a > k):")
for (k,a,b) in [(2,3,4),(2,3,5),(2,4,5),(3,4,5),(3,4,6),(2,5,7),(3,5,6)]:
    t=k+1
    if t>n: continue
    m_hba=0; m_ratio_reduced=0; m_hquotient=0; tot=0; ex=None
    for T in itertools.combinations(range(n),t):
        ra=residual(dom,k,T,a,q); rb=residual(dom,k,T,b,q)
        if ra%q==0: continue
        tot+=1
        gam=(-rb)*pow(ra,q-2,q)%q
        roots=[dom[i] for i in T]
        redb=poly_mod_coreVanish(b,roots,q); reda=poly_mod_coreVanish(a,roots,q)
        # ratio from reduced coeffs (this is the TRUE controlling object, always holds)
        if reda[k]%q:
            pred=(-redb[k])*pow(reda[k],q-2,q)%q
            if pred==gam: m_ratio_reduced+=1
        # single h_{b-a}?
        if gam==(-h_complete(b-a,roots,q))%q: m_hba+=1
        # ratio of h's: -h_{b-k}/h_{a-k}?  (Jacobi-Trudi: reducedcoeff_e[k] relates to h_{e-k})
        ha=h_complete(a-k,roots,q); hb=h_complete(b-k,roots,q)
        if ha%q:
            predh=(-hb)*pow(ha,q-2,q)%q
            if predh==gam: m_hquotient+=1
        if ex is None: ex=(T,gam,(-h_complete(b-a,roots,q))%q)
    print(f"  (k={k},a={a},b={b}) gap={b-a}: ratio==-redCoeff_b/redCoeff_a:{m_ratio_reduced}/{tot}"
          f" | ratio==-h_{{{b-a}}}:{m_hba}/{tot} | ratio==-h_{{{b-k}}}/h_{{{a-k}}}:{m_hquotient}/{tot}")

print()
print("CONCLUSION TEST: is the controlling object a single h_{b-a} (connection's claim),")
print("or the Jacobi-Trudi cofactor ratio -h_{b-k}/h_{a-k} (which collapses to -h_{b-a} ONLY at a=k)?")
