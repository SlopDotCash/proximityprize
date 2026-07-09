#!/usr/bin/env python3
r"""
probe_resonant_spike_vs_B_407.py  (#407)

The worst-case face-3 ratio spiked to 34.5 at n=32,r=3,p=194977.  Two honest questions:
 (1) At that SAME resonant prime, is the actual house B = max_b|S(b)| still ~ sqrt(n log m)?
     (i.e. does a single-r defect spike translate into an anomalously LARGE Gauss period,
      or does it cancel out so B stays on the law?)  This decides whether the spike is a
     real threat to the prize floor or a single-r artifact that the max washes out.
 (2) Track B/sqrt(n*ln m) at the resonant prime vs a generic nearby prime.
"""
import math, numpy as np
import sympy

def subgroup(p,n):
    g=int(sympy.primitive_root(p)); h=pow(g,(p-1)//n,p)
    H=[]; x=1
    for _ in range(n): H.append(x); x=x*h%p
    return H

def house_and_moments(p,n,rmax):
    f=np.zeros(p)
    for x in subgroup(p,n): f[x]=1.0
    S=np.fft.fft(f); a2=np.abs(S)**2
    a2[0]=0.0
    B=float(np.sqrt(np.max(a2)))
    Es={r: float(np.sum((np.abs(S)**2)**r)/p) for r in range(1,rmax+1)}
    return B, Es

print("=== Does the r=3 resonant spike show up in the actual house B? (#407) ===\n")
cases = [
    (32, 194977, "RESONANT (face3 r=3 = 34.5)"),
    (32, 195073, "generic nearby"),
    (32, 32609,  "generic p~n^3"),
    (16, 41521,  "RESONANT (face3 r=3 = 1.19)"),
    (16, 41617,  "generic nearby"),
]
print(f"{'n':>4} {'p':>9} {'m=(p-1)/n':>10} {'B':>8} {'sqrt(n*lnm)':>11} "
      f"{'C=B/that':>9} {'B/sqrt(n)':>10}  note")
for (n,p,note) in cases:
    if (p-1)%n!=0 or not sympy.isprime(p):
        # adjust to nearest valid prime = 1 mod n at or below
        q=p-((p-1)%n)
        while not (sympy.isprime(q) and (q-1)%n==0): q-=n
        p=q; note+=f" [adj p={p}]"
    m=(p-1)//n
    B,_=house_and_moments(p,n,1)
    law=math.sqrt(n*math.log(max(m,2)))
    C=B/law if law>0 else float('nan')
    print(f"{n:>4} {p:>9} {m:>10} {B:>8.3f} {law:>11.3f} {C:>9.3f} {B/math.sqrt(n):>10.3f}  {note}")
print("\nREAD: if C=B/sqrt(n ln m) at the resonant prime is in the SAME ~1.0-1.5 band as the")
print("      generic primes, the r=3 face-3 spike is a single-low-moment artifact that does NOT")
print("      lift to an anomalous house -- so the prize floor (governed by B) is NOT threatened by it.")
