#!/usr/bin/env python3
r"""
probe_face3_worstcase_407.py  (#407)

HONEST worst-case stress test of the prize floor (face 3):  D_r(q) <= n^{2r}/q ?
We scan ALL primes p = 1 mod n in a band and report the MAX of D_r/(n^{2r}/q).
If this max is comfortably <=1, the floor holds empirically; if it spikes >> 1 at
resonant primes, the worst-case floor is FALSE (the average holds but not the max) --
either way an honest datum.  (The prior session reported occasional pts > 1; we pin how big.)

Also: the SUM-RULE.  Sum over ALL nonzero cosets of |S(b)|^{2r} = p*E_r.  The defect total
sum_b (over the (p-1)/n periods, each with multiplicity n) ... we just track the global
worst single ratio and the average, to bound the spread.
"""
import math, itertools
from collections import Counter
import sympy

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

def subgroup(p,n):
    g=int(sympy.primitive_root(p)); h=pow(g,(p-1)//n,p)
    H=[]; x=1
    for _ in range(n): H.append(x); x=x*h%p
    return H

def E_r_mod_q(p,H,r):
    cnt=Counter()
    for xx in itertools.product(H,repeat=r):
        cnt[sum(xx)%p]+=1
    return sum(c*c for c in cnt.values())

print("=== WORST-CASE face-3 floor stress test: max_p D_r/(n^2r/q) (#407) ===\n")
print("If the prize floor D_r <= n^2r/q holds worst-case, this max stays <= ~1.\n")
print(f"{'n':>4} {'r':>2} {'band':>20} {'#primes':>8} {'maxRatio':>9} {'@p':>9} "
      f"{'avgRatio':>9} {'#defect_p':>10}")
configs = [(8,3),(8,4),(16,3),(16,4),(32,3)]
for (n,r) in configs:
    Ec=E_r_complex_brute(n,r)
    lo, hi = n*n, min(n**4, 200000)
    ps=[k*n+1 for k in range(lo//n, hi//n+1) if sympy.isprime(k*n+1) and k*n+1>1]
    if not ps: continue
    maxr=-1; argp=0; ssum=0.0; cnt=0; ndef=0
    for p in ps:
        H=subgroup(p,n)
        Eq=E_r_mod_q(p,H,r)
        D=Eq-Ec
        rand=n**(2*r)/p
        ratio=D/rand
        ssum+=ratio; cnt+=1
        if D>0: ndef+=1
        if ratio>maxr: maxr=ratio; argp=p
    print(f"{n:>4} {r:>2} {f'[{lo},{hi}]':>20} {len(ps):>8} {maxr:>9.4f} {argp:>9} "
          f"{ssum/cnt:>9.4f} {ndef:>10}")
print("\nREAD: maxRatio is the worst-case face-3 floor over the band.  Spikes > 1 mean the")
print("      worst-case floor is not clean (resonant primes); how big the spike is = how far")
print("      a worst-case bound would have to be relaxed from the random baseline.")
