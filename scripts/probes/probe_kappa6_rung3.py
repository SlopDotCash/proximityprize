#!/usr/bin/env python3
"""
probe_kappa6_rung3.py (#444) — pin the HONEST r=3 rung statement and its char-p robustness.

Resolved claim:  the r=3 Wick rung is  E_3(mu_n) <= 15 n^3, equivalently the Wick DEFECT
   D_3 := 15 n^3 - E_3   satisfies   D_3 = 45 n^2 - 40 n   in CHAR 0  (n even),  so  D_3 <= 45 n^2.
This is the precise content of "kappa6 <= 45 n^2": kappa6 := the Wick defect 15n^3 - E3 (+lower terms).

Two questions:
  (Q1) char-p robustness: does E_3 <= 15 n^3 SURVIVE in char p even when the exact char-0 form
       E_3 = 15n^3-45n^2+40n FAILS (the defect cases n=12,24)?  i.e. is the DEFECT one-sided
       (E3 only goes UP toward 15n^3, never above)?
  (Q2) 4|n vs n=2 mod 4 (proper subgroup, both negation-closed) — does the closed form hold?
"""
from sympy import isprime
from collections import Counter

def primitive_root(p):
    phi=p-1; m=phi; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def energies(p,n):
    g=primitive_root(p); step=pow(g,(p-1)//n,p)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*step)%p
    s3=Counter()
    for a in mu:
        for b in mu:
            ab=(a+b)%p
            for c in mu: s3[(ab+c)%p]+=1
    E3=sum(v*v for v in s3.values())
    return E3

def sweep_primes(n, k_lo, count):
    """smallest `count` primes p=n*k+1 with k>=k_lo and p >> n^3."""
    out=[]; k=max(k_lo,(60*n**3)//n+1)
    while len(out)<count:
        p=n*k+1
        if isprime(p): out.append(p)
        k+=1
    return out

print("Q1 — char-p ROBUSTNESS of the rung E_3 <= 15 n^3 (sweep several primes per n):")
print(f"{'n':>4} {'n%4':>4} {'#primes':>8} {'min E3':>10} {'max E3':>10} {'15n^3':>10} {'all<=15n^3?':>12} {'c0 form hits?':>13}")
worst_ratio=0.0
allok=True
for n in [4,8,12,16,20,24,28,32,36,40]:
    ps=sweep_primes(n, 2, 6)
    es=[energies(p,n) for p in ps]
    w=15*n**3
    c0=15*n**3-45*n**2+40*n
    ok=all(e<=w for e in es)
    allok = allok and ok
    hits_c0 = c0 in es
    for e in es: worst_ratio=max(worst_ratio, e/w)
    print(f"{n:>4} {n%4:>4} {len(ps):>8} {min(es):>10} {max(es):>10} {w:>10} {str(ok):>12} {str(hits_c0):>13}")
print(f"\nALL E3 <= 15 n^3 across sweep? {allok}    worst E3/(15n^3) = {worst_ratio:.4f}")
print()
print("Q2 — exact closed form by residue of n mod 4 (does 4|n matter for E3 char-0 value?):")
print(f"{'n':>4} {'n%4':>4} {'E3 char-p (clean p)':>20} {'15n^3-45n^2+40n':>18} {'match?':>8}")
for n in [4,6,8,10,12,14,16,18,20]:
    # pick a 'clean' prime: large multiplier reduces structured-collision chance
    ps=sweep_primes(n, 2, 8)
    es=[energies(p,n) for p in ps]
    # the char-0 / minimal value is the min (defects only inflate E3)
    Emin=min(es)
    c0=15*n**3-45*n**2+40*n
    print(f"{n:>4} {n%4:>4} {Emin:>20} {c0:>18} {str(Emin==c0):>8}")
