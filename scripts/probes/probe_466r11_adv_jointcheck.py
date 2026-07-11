#!/usr/bin/env python3
"""
ADVERSARIAL recheck of Lane J worker verdict. Three independent tests:

TEST 1 (is the worker's collinearity the trivial neg-closed artifact?):
  The worker's A_b = eta_b(Hlow), B_b = eta_{zeta b}(Hlow) where Hlow = {h^{2i}} = even powers.
  Hlow is negation-closed iff -1 = h^{n/2} in Hlow, i.e. n/2 even, i.e. 4|n. Then EACH of A_b,B_b
  is REAL up to the SAME global phase, so collinearity is FORCED and is the known
  eta_real_of_neg_closed / probe_407_phase_dichotomy fact, NOT new. Verify: measure max|Im| of
  A_b, B_b after dividing out the global phase e_p(0)=1 (Hlow contains 1 so period is real outright).

TEST 2 (does the object Round 10 ACTUALLY flagged escape?):
  Round 10 flagged (eta_b, eta_{zeta b}) = two FULL periods over mu_n at ADJACENT cosets. mu_n is
  NOT negation-closed in general? Actually -1=h^{n/2} IS in mu_n. So full periods are ALSO real.
  But the JOINT of two adjacent FULL periods: are eta_b(mu_n) and eta_{zeta b}(mu_n) collinear?
  Both real (up to nothing, since mu_n negation-closed => eta real) => trivially collinear too.
  Measure directly.

TEST 3 (the worker's own flagged residue -- the negation-OPEN sub-tower):
  Take a half-period over an ODD coset shift H1 = h*Hlow = {h^{2i+1}} (odd powers). This is NOT
  negation-closed (h^{2i+1} negated = -h^{2i+1} = h^{n/2+2i+1}, exponent parity n/2+odd; if n/2 odd
  i.e. n=2 mod 4 this stays odd->closed, if n/2 even i.e. 4|n then n/2+odd=odd->CLOSED too!).
  Hmm. Actually the ODD coset is negation-closed iff n/2 even. Let me just MEASURE whether any
  natural sub-tower half over a non-neg-closed set gives a GENUINELY 2D (non-collinear) joint,
  and whether at the prize all dyadic levels are neg-closed (worker's vacuity claim).
  Concretely test a QUARTER split: C0={h^{4i}}, C1={h^{4i+1}},... These 4 sets: is C1 neg-closed?
  -h^{4i+1}=h^{n/2+4i+1}; n/2 mod 4 determines coset. For 4|n, n/2 even; n/2 mod4 in {0,2}.
  If n/2=2 mod4, -C1=C3 (NOT self => C1 not neg-closed => eta_{C1} COMPLEX). Test collinearity of
  the pair (eta_b(C1), eta_{zeta b}(C1)) then: genuinely 2D?
"""
import numpy as np

def isprime(m):
    if m<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def v2(x):
    k=0
    while x%2==0:k+=1;x//=2
    return k
def primroot(p):
    fac=set();mm=p-1;d=2
    while d*d<=mm:
        if mm%d==0:
            fac.add(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fac.add(mm)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac):return a
def _pf(n):
    f=set();d=2;m=n
    while d*d<=m:
        if m%d==0:
            f.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1:f.add(m)
    return f
def find_primes(n,beta=4,count=3):
    out=[];p=(n**beta)//n*n+1;need=v2(n)
    while len(out)<count:
        if p>n and isprime(p) and (p-1)%n==0 and v2(p-1)>=need:
            g=primroot(p);h=pow(g,(p-1)//n,p)
            if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in _pf(n)):
                out.append(p)
        p+=n
    return out

def period(p, elems, b):
    tp=2*np.pi/p
    e=np.array(elems,dtype=np.int64)
    return np.exp(1j*tp*((b*e)%p)).sum()

for n in (8,16,32):
    primes=find_primes(n,beta=4,count=2)
    print(f"\n{'='*76}\nn={n}  primes={primes}  n/2 mod4={ (n//2)%4 }\n{'='*76}")
    for p in primes:
        g=primroot(p);h=pow(g,(p-1)//n,p)
        m=(p-1)//n
        breps=[pow(g,i,p) for i in range(m)]
        Hlow=[pow(h,2*i,p) for i in range(n//2)]         # even powers (worker's A/B set)
        MuN =[pow(h,i,p) for i in range(n)]              # full subgroup
        # TEST 1: worker's A,B individually real?
        imA=max(abs(period(p,Hlow,b).imag) for b in breps[:200])
        # TEST 2: two adjacent FULL periods eta_b(muN), eta_{hb}(muN) -- collinear? (both real=>yes)
        imFull=max(abs(period(p,MuN,b).imag) for b in breps[:200])
        # collinearity of adjacent full pair:
        sinmaxFull=0.0
        for b in breps[:400]:
            F0=period(p,MuN,b); F1=period(p,MuN,(h*b)%p)
            cr=(F1*np.conj(F0))
            if abs(F0)>1e-9 and abs(F1)>1e-9:
                sinmaxFull=max(sinmaxFull, abs(cr.imag)/(abs(F0)*abs(F1)))
        # TEST 3: quarter split C1 = {h^{4i+1}} -- neg-closed?
        C1=[pow(h,4*i+1,p) for i in range(n//4)] if n>=4 else None
        imC1=None; sinmaxC1=None; genuine2d=None
        if C1 is not None and n//4>=1:
            imC1=max(abs(period(p,C1,b).imag) for b in breps[:200])
            # joint of (eta_b(C1), eta_{hb}(C1)): collinear?
            sm=0.0; sample=0
            for b in breps[:600]:
                F0=period(p,C1,b); F1=period(p,C1,(h*b)%p)
                if abs(F0)>1e-9 and abs(F1)>1e-9:
                    cr=(F1*np.conj(F0)); sm=max(sm,abs(cr.imag)/(abs(F0)*abs(F1))); sample+=1
            sinmaxC1=sm
            genuine2d = sm>1e-6
        print(f"  p={p:>9} m={m}: [T1] max|Im A_b(Hlow)|={imA:.2e} (real=>trivially collinear)")
        print(f"            [T2] max|Im eta_b(muN)|={imFull:.2e}  adj-full |sin|max={sinmaxFull:.2e}")
        if C1 is not None:
            neg = "NEG-CLOSED(real)" if imC1<1e-6 else "NOT neg-closed(COMPLEX)"
            print(f"            [T3] C1={{h^(4i+1)}} max|Im|={imC1:.2e} {neg}"
                  f"  adj-pair |sin|max={sinmaxC1:.2e} genuine2D={genuine2d}")
print("\nINTERPRETATION:")
print(" T1/T2: if A_b, eta_b(muN) are REAL (|Im|~0), collinearity is the TRIVIAL neg-closed fact")
print("        (eta_real_of_neg_closed), already in DISPROOF_LOG. Worker's 'collinear' finding is")
print("        that known artifact, NOT a new deep-r structure.")
print(" T3: if a non-neg-closed sub-tower gives genuine2D=True, phase IS 2D there -- but check if")
print("     such a level is reachable in the dyadic prize tower (worker says no: vacuous).")
