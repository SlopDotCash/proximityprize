#!/usr/bin/env python3
"""C008: do prize-form prime factors (q=1 mod n, mu_n proper) land in the target
beta in [4,5] band, and how does the spectrum's max prime scale? This shows the
'finite divisor set' is dense with prize-sized primes across the whole beta range."""
from sympy import factorint
from sympy import symbols, Poly, resultant
import math, random
from itertools import combinations
X=symbols('X')

def res_val(m,A):
    n=2**m; h=2**(m-1); coeff=[0]*h; Al=sorted(A)
    for a in range(len(Al)):
        for b in range(a+1,len(Al)):
            e=(Al[a]+Al[b])%n
            if e<h: coeff[e]+=1
            else: coeff[e-h]-=1
    p_ef=Poly(list(reversed(coeff)),X,domain='ZZ')
    cyc=[0]*(h+1); cyc[0]=1; cyc[-1]=1
    return int(resultant(p_ef.as_expr(),Poly(cyc,X,domain='ZZ').as_expr(),X))

def prize_form_factors(m, A):
    n=2**m; R=res_val(m,A)
    if R==0: return []
    out=[]
    for p,_ in factorint(abs(R)).items():
        if p%2==1 and p%n==1 and p>n:
            out.append((p, math.log(p,n)))   # (prime, beta)
    return out

random.seed(7)
for m, size, ns in [(5,12,150),(5,16,150),(6,16,40),(6,24,40)]:
    n=2**m; uni=list(range(n))
    betas=[]; primes_in_band=[]
    for _ in range(ns):
        A=random.sample(uni,size)
        for (p,b) in prize_form_factors(m,set(A)):
            betas.append(b)
            if 4.0<=b<=5.0: primes_in_band.append((p,round(b,2)))
    if betas:
        print(f"n={n} |A|={size}: {len(betas)} prize-form factors over {ns} subsets; "
              f"beta range [{min(betas):.2f},{max(betas):.2f}], "
              f"#in band[4,5]={len(primes_in_band)}")
        if primes_in_band:
            print(f"    sample band[4,5] prize primes (q=1 mod {n}, proper subgroup): "
                  f"{primes_in_band[:4]}")
    else:
        print(f"n={n} |A|={size}: no prize-form factors in {ns} samples")
