#!/usr/bin/env python3
r"""
probe_true_defect_onset_407.py  (#407)

CORRECTED probe.  Uses the TRUE char-0 energy E_r^C (brute, via the reduced coeff vector
in Q(zeta_n), dim n/2) as the baseline, and the TRUE defect D_r = E_r^{F_q} - E_r^C >= 0.

We pin, as a function of (n=2^a, r, q):
  1. the exact char-0 energy E_r^C(mu_n)  -- and fit its leading term (is it ~ (2r-1)!! n^r ? smaller?)
  2. the defect D_r(q) >= 0 and the face-3 ratio  D_r / (n^{2r}/q)   (prize floor <=> <=1 at r~ln q)
  3. the ONSET: smallest q (= sparsest p) at which D_r becomes nonzero, vs the predicted
     norm threshold q > a^{n/2} (a = max house = 2r).  Below threshold no defect (norm bound);
     above, defects appear.  We test whether onset matches.
  4. THE DESCENT TEST: D_r(mu_n) vs D_r(mu_{n/2}) at the SAME q.  A working descent would give
     D_r(mu_n) <= C * D_r(mu_{n/2}) + (cheap term).  We report the ratio.
"""
import numpy as np, math, itertools
from collections import Counter

def is_prime(x):
    if x<2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x%w==0: return x==w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(w,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True

def prime_1_mod_n_near(t,n):
    p=t-(t%n)+1
    if p>t: p-=n
    while p>n:
        if is_prime(p): return p
        p-=n
    return None

def E_r_complex_brute(n, r):
    half=n//2
    cnt=Counter()
    for x in itertools.product(range(n), repeat=r):
        v=[0]*half
        for a in x:
            if a<half: v[a]+=1
            else: v[a-half]-=1
        cnt[tuple(v)]+=1
    return sum(c*c for c in cnt.values())

def E_r_mod_q_subgroup(p, n, r):
    import sympy
    g=int(sympy.primitive_root(p)); h=pow(g,(p-1)//n,p)
    H=[]; x=1
    for _ in range(n): H.append(x); x=x*h%p
    cnt=Counter()
    for xx in itertools.product(H, repeat=r):
        cnt[sum(xx)%p]+=1
    return sum(c*c for c in cnt.values())

print("=== TRUE char-0 energy and TRUE defect onset (#407) ===\n")
print("Part 1: exact char-0 energy E_r^C(mu_n)  (vs (2r-1)!!n^r upper bound)")
print(f"{'n':>4} {'r':>2} | {'E_r^C':>10} {'(2r-1)!!n^r':>12} {'E_r^C/n^r':>10} {'(2r-1)!!':>9}")
for a in (1,2,3,4,5):
    n=2**a
    for r in (1,2,3,4):
        if n**r > 1_500_000: continue
        Ec=E_r_complex_brute(n,r)
        dfac=1; k=2*r-1
        while k>1: dfac*=k; k-=2
        print(f"{n:>4} {r:>2} | {Ec:>10} {dfac*n**r:>12} {Ec/n**r:>10.4f} {dfac:>9}")

print("\nPart 2 + 4: defect D_r(q)>=0, face-3 ratio, and tower-descent ratio D_r(n)/D_r(n/2) at same q.")
print(f"{'n':>4} {'r':>2} {'p':>9} | {'E_r^C':>10} {'E_r^Fq':>10} {'D_r':>8} "
      f"{'D_r/(n^2r/q)':>13} {'D_r(n)/D_r(n/2)':>16}")
for a in (2,3,4,5):
    n=2**a
    p=prime_1_mod_n_near(n**3,n)
    if p is None or p>2_000_000: continue
    Dvals={}
    for nn in (n, n//2):
        for r in (2,3):
            if nn**r > 1_500_000: continue
            Ec=E_r_complex_brute(nn,r)
            Eq=E_r_mod_q_subgroup(p,nn,r)
            D=Eq-Ec
            rand=nn**(2*r)/p
            ratio = D/rand if rand>0 else float('nan')
            Dvals[(nn,r)]=D
            if nn==n:
                desc=""
                if (n//2,r) in Dvals and Dvals[(n//2,r)]>0:
                    desc=f"{D/Dvals[(n//2,r)]:.3f}"
                elif (n//2,r) in Dvals:
                    desc=f"{D}/{Dvals[(n//2,r)]}"
                print(f"{n:>4} {r:>2} {p:>9} | {Ec:>10} {Eq:>10} {D:>8} "
                      f"{ratio:>13.4f} {desc:>16}")
