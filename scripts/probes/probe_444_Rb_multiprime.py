#!/usr/bin/env python3
"""
R-b POINT (i) DECISIVE: the multi-prime exponent.  Directly construct antipodal-free sets C
and impose p_1(C)=p_3(C)=...=0 (the odd conditions), then check v_p(N(beta_C)) == #odd-conditions.

Strategy: forget the full S; just look for an antipodal-free C in mu_n with the FIRST few odd
power sums = 0 mod p (this is EXACTLY the object beta_C the floor's step 2 bounds, regardless of
whether C extends to a full vanishing S).  For each such C, compute v_p(N(beta_C)) and compare to
the number of odd conditions imposed (= ceil(c/2)).  Then test: does imposing MORE odd conditions
strictly raise v_p(N) by 1 each time, or can dependencies stall it (exponent short)?

We scan n=16,32 and for each prime collect antipodal-free C (sizes 3..6) with p_1=0; among those
also with p_3=0 (=> 2 odd conditions); among those also with p_5=0 (=> 3).  Report v_p(N) by class.
"""
import itertools, sys
from sympy import isprime, primitive_root, symbols, Poly, resultant, cyclotomic_poly, ZZ
from collections import Counter, defaultdict

_X=symbols('x')
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p); e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def norm(idxs,n):
    cnt=Counter(i%n for i in idxs)
    B=Poly(sum(co*_X**e for e,co in cnt.items()),_X,domain=ZZ)
    Phi=Poly(cyclotomic_poly(n,_X),_X,domain=ZZ)
    return int(resultant(Phi,B))
def vp(N,p):
    if N==0: return -1
    v,a=0,abs(N)
    while a%p==0: a//=p; v+=1
    return v
def antipodal_free(C,p):
    s=set(C); return all((p-x)%p not in s for x in C)

for n in [16,32]:
    primes=[p for p in range(n+1,300) if isprime(p) and (p-1)%n==0][:5]
    print(f"\n=== n={n} ===", flush=True)
    for p in primes:
        elts=subgroup(n,p); im={x:i for i,x in enumerate(elts)}
        # classify antipodal-free C by how many leading odd power sums vanish, track v_p(N)
        # buckets: number of odd conditions satisfied among j=1,3,5
        stat=defaultdict(list)  # n_odd_conditions -> list of v_p(N)
        anomalies=[]
        for sz in [3,4,5,6]:
            for C in itertools.combinations(elts,sz):
                if not antipodal_free(C,p): continue
                pj={j: sum(pow(x,j,p) for x in C)%p for j in [1,3,5]}
                # count consecutive leading odd conditions satisfied
                k=0
                for j in [1,3,5]:
                    if pj[j]==0: k+=1
                    else: break
                if k==0: continue
                idxs=[im[x] for x in C]
                v=vp(norm(idxs,n),p)
                stat[k].append(v)
                # ANOMALY: if k odd conditions satisfied but v_p(N) < k -> exponent short
                if v>=0 and v<k:
                    anomalies.append((sz,k,v,sorted(idxs)))
        for k in sorted(stat):
            vs=stat[k]
            mn=min(vs); mx=max(vs)
            short = mn < k
            print(f"  p={p}: #leading-odd-conds={k}: count={len(vs)} v_p(N) range [{mn},{mx}] "
                  f"(need>= {k}) {'<<<< SHORT EXPONENT!' if short else 'OK'}", flush=True)
        for a in anomalies[:5]:
            print(f"      ANOMALY sz={a[0]} k_odd={a[1]} v_p={a[2]} idx={a[3]}", flush=True)
print("\nDONE", flush=True)
