#!/usr/bin/env python3
"""
probe_kappa6_rung2.py  (Issue #444) — resolve what "kappa6" means so the task identity holds.

Task asserts TWO things simultaneously:
  (I)  A_3 = kappa6 - 45 n^2 + 15 n^3       (for 4|n symmetric)
  (II) kappa6 = O(n^2), coefficient ~0.4..1.2, "far below 45 EVERYWHERE"

Known EXACT char-0 (n even): E_3 = 15 n^3 - 45 n^2 + 40 n.
With A_3 -> E_3 (p->inf), (I) forces  kappa6 = E_3 - 15 n^3 + 45 n^2 = 40 n   (LINEAR, not n^2).

So (I)+(II) are INCOMPATIBLE under the EXACT char-0 form.  This probe enumerates candidate
"kappa6" objects and reports which (if any) is BOTH O(n^2) with coeff ~0.4..1.2 AND <= 45 n^2,
to find the honest statement.

Candidates for the connected 6th cumulant of eta_b (b uniform, DC-subtracted):
  raw power sums  S_r = sum_{b!=0} |eta_b|^{2r} = p E_r - n^{2r}
  central moments of X=|eta_b|^2 about its mean over b!=0.
"""
from fractions import Fraction as Fr
from sympy import isprime

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

def eta_periods(p,n):
    """Return list of |eta_b|^2 for ALL b != 0 (length p-1)."""
    import cmath, math
    g=primitive_root(p); step=pow(g,(p-1)//n,p)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*step)%p
    out=[]
    w=2*math.pi/p
    for b in range(1,p):
        re=0.0; im=0.0
        for x in mu:
            ang=w*((b*x)%p)
            re+=math.cos(ang); im+=math.sin(ang)
        out.append(re*re+im*im)
    return out

def energies_charp(p,n):
    from collections import Counter
    g=primitive_root(p); step=pow(g,(p-1)//n,p)
    mu=[]; x=1
    for _ in range(n):
        mu.append(x); x=(x*step)%p
    E1=n
    s2=Counter()
    for a in mu:
        for b in mu: s2[(a+b)%p]+=1
    E2=sum(v*v for v in s2.values())
    s3=Counter()
    for a in mu:
        for b in mu:
            ab=(a+b)%p
            for c in mu: s3[(ab+c)%p]+=1
    E3=sum(v*v for v in s3.values())
    return E1,E2,E3

def find_prime(n, factor=60):
    k=max(2,(factor*n**3)//n+1)
    while True:
        p=n*k+1
        if isprime(p): return p
        k+=1

print("Resolving kappa6 — candidate connected objects, EXACT char-p energies (p >> n^3):")
print()
hdr=f"{'n':>4} {'p':>9} | {'E3-15n^3+45n^2':>15} | {'central3(X)':>13} | {'cum3raw/p':>11} | {'cum6/n^2':>9}"
print(hdr); print("-"*len(hdr))
for n in [4,8,12,16,20,24,28,32]:
    p=find_prime(n)
    E1,E2,E3=energies_charp(p,n)
    # candidate 1: the task-forced value from (I): kappa6 = E3 - 15n^3 + 45n^2  (-> 40n char-0)
    cand1 = E3 - 15*n**3 + 45*n**2
    # central moments of X=|eta_b|^2 over b != 0 (exact via energies):
    # E[X^r] = S_r/(p-1), S_r = p E_r - n^{2r}
    m1 = Fr(p*E1 - n**2, p-1)
    m2 = Fr(p*E2 - n**4, p-1)
    m3 = Fr(p*E3 - n**6, p-1)
    # central 3rd moment mu3c = m3 - 3 m1 m2 + 2 m1^3  (= classical 3rd cumulant of X)
    cum3 = m3 - 3*m1*m2 + 2*m1**3
    # raw-cumulant divided by p (per-period connected)
    # the "6th cumulant of eta" as classical k3 of raw S_r/p:
    a1=Fr(p*E1-n**2,p); a2=Fr(p*E2-n**4,p); a3=Fr(p*E3-n**6,p)
    cum3_raw = a3 - 3*a1*a2 + 2*a1**3
    print(f"{n:>4} {p:>9} | {cand1:>15} | {float(cum3):>13.2f} | {float(cum3_raw/p):>11.4f} | {float(cum3)/n**2:>9.4f}")

print()
print("Interpretation:")
print(" - candidate (I)-forced kappa6 = E3-15n^3+45n^2 -> 40n  (LINEAR in n; NOT O(n^2)).")
print(" - classical 3rd cumulant of X=|eta|^2 (central3) -> grows like the raw E3 ~ 15n^3 (cubic).")
print(" => The task's '(I) AND kappa6=O(n^2),coeff 0.4-1.2' are INCONSISTENT with exact char-0 E3.")
print()
print("HONEST rung that IS exact & decidable in char-0 clean regime:  E_3 <= 15 n^3  (Wick, r=3),")
print("equivalently  A_3 = E_3 - n^6/p <= 15 n^3.  This is what 'A_3 <= Wick at r=3' means.")
print()
# verify the clean Wick rung E3 <= 15 n^3 exactly, char-p:
print(f"{'n':>4} {'p':>9} {'E3(cp)':>12} {'15n^3':>12} {'E3<=15n^3?':>11} {'15n^3-E3':>10} {'=45n^2-40n?':>12}")
for n in [4,8,16,20,28,32]:
    p=find_prime(n)
    _,_,E3=energies_charp(p,n)
    w=15*n**3
    gap=w-E3
    print(f"{n:>4} {p:>9} {E3:>12} {w:>12} {str(E3<=w):>11} {gap:>10} {str(gap==45*n**2-40*n):>12}")
