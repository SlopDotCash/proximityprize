#!/usr/bin/env python3
r"""
probe_defect_onset_threshold_407.py  (#407)

Pin the p-DEFECT ONSET precisely and test the descent.

A defect at order 2r is a relation sum_{i<=r} g^{x_i} = sum g^{y_i} mod q that is NOT a
char-0 relation, i.e. alpha := sum zeta^{x_i} - sum zeta^{y_i} != 0 in C  but  q | N-image.
alpha is in Z[zeta_n], a sum of <= 2r roots of unity, so HOUSE(alpha) <= 2r and every
conjugate |sigma(alpha)| <= 2r.  A defect requires q | alpha in the prime above q, hence
(taking norms over the ENTIRE field, all phi(n)=n/2 conjugates) q <= |Norm(alpha)| <= (2r)^{n/2}.
=> NO defects of order 2r when q > (2r)^{n/2}   (the norm/house threshold).

PRIZE: q ~ n*2^128, n=2^mu, mu up to 40, r ~ ln q ~ 180.  Threshold (2r)^{n/2} = (360)^{2^39}
is ASTRONOMICALLY larger than q -- so the norm bound is VACUOUS at the prize and defects CAN
appear.  The question is whether their COUNT stays <= n^{2r}/q (the random baseline).

This probe, at small n where we can brute-force:
  (A) confirms the threshold: scan primes p = 1 mod n from large (sparse) to small (dense),
      report the largest p with D_r > 0  (onset) and compare to (2r)^{n/2} and to n^{2r}/q~1.
  (B) at primes where BOTH mu_n and mu_{n/2} have defects, report D_r(n)/D_r(n/2) (descent ratio).
  (C) the face-3 ratio D_r/(n^{2r}/q) across the onset window: does it stay <=1 (prize floor)
      or blow up just past onset?
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

def primes_1_mod_n(n, lo, hi):
    out=[]
    k=lo//n
    while k*n+1 <= hi:
        p=k*n+1
        if p>1 and sympy.isprime(p): out.append(p)
        k+=1
    return out

print("=== p-DEFECT ONSET THRESHOLD + descent (#407) ===\n")

# (A)+(C): onset scan at n=16, r=3 (the first level that shows defects at p~n^3).
for (n, r) in [(16,3),(32,3),(16,4)]:
    if n**r > 2_000_000:  # E_r^C brute and mod-q both ~ n^r work; n^4 for 16 = 65536 ok? 16^4=65536 fine, 32^3=32768 fine
        pass
    Ec = E_r_complex_brute(n, r)
    half=n//2
    thresh = (2*r)**half  # norm/house threshold: no defect when q>thresh
    print(f"--- n={n}, r={r}:  E_r^C={Ec},  norm-threshold (2r)^(n/2)=({2*r})^{half}={thresh:.3e}")
    print(f"    {'p':>9} {'p/thresh':>10} {'D_r':>9} {'n^2r/q':>12} {'D_r/(n^2r/q)':>13} {'defect?':>8}")
    # scan a band of primes around n^3 down toward where defects turn on/off
    ps = primes_1_mod_n(n, n*n, min(n**4, 600000))
    # subsample to keep runtime ok: take ~20 spread across the range
    if len(ps) > 24:
        idx = [int(i*(len(ps)-1)/23) for i in range(24)]
        ps = [ps[i] for i in idx]
    shown=0
    for p in ps:
        H=subgroup(p,n)
        Eq=E_r_mod_q(p,H,r)
        D=Eq-Ec
        rand = n**(2*r)/p
        ratio = D/rand if rand>0 else float('nan')
        if D>0 or shown<3 or p==ps[-1]:
            print(f"    {p:>9} {p/thresh:>10.2e} {D:>9} {rand:>12.2f} {ratio:>13.4f} {str(D>0):>8}")
            if D>0: shown+=1
    print()

# (B): descent ratio at a fixed dense prime where both n and n/2 have defects.
print("--- DESCENT TEST: at the densest tractable prime, D_r(mu_n)/D_r(mu_{n/2}) and the")
print("    face-3 ratio at each level (does the defect CONCENTRATE at the top level, i.e.")
print("    is D_r(n) >> D_r(n/2), so a descent to n/2 would LOSE the bulk?).")
print(f"    {'n':>4} {'r':>2} {'p':>9} | {'D_r(n)':>9} {'D_r(n/2)':>9} {'ratio n:(n/2)':>14} "
      f"{'face3(n)':>9} {'face3(n/2)':>11}")
for (n,r) in [(16,3),(32,3),(16,4)]:
    # pick a denser prime to force defects at both levels: ~ n^2.6
    p = None
    for cand in primes_1_mod_n(n, int(n**2.4), int(n**2.8)):
        p = cand  # take the largest in band
    if p is None: continue
    Dn={}; f3={}
    for nn in (n, n//2):
        Ec=E_r_complex_brute(nn,r)
        H=subgroup(p,nn)
        Eq=E_r_mod_q(p,H,r)
        D=Eq-Ec
        Dn[nn]=D
        rand=nn**(2*r)/p
        f3[nn]=D/rand if rand>0 else float('nan')
    rr = f"{Dn[n]/Dn[n//2]:.3f}" if Dn[n//2]>0 else f"{Dn[n]}/{Dn[n//2]}"
    print(f"    {n:>4} {r:>2} {p:>9} | {Dn[n]:>9} {Dn[n//2]:>9} {rr:>14} "
          f"{f3[n]:>9.3f} {f3[n//2]:>11.3f}")
