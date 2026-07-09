#!/usr/bin/env python3
"""_wf_Ek_randomlike_deeparrow.py  (#407 — Ek-randomlike, CLOSEOUT: deep-r + arrow at worst prime)

Settles the LAST piece: at the WORST fixed-index prime (the structured resonance), does
  (i) c_r stay FLAT as r -> log-q depth (no deep-moment inflation), and
  (ii) the moment arrow min_r (p*E_r')^{1/2r}  (E_r' = E_r minus b=0 main term) still track the true
       sup B and the clean law sqrt(n log(p/n)) within a BOUNDED factor?
If both hold even at the worst prime, the moment method is not killed by E_r non-randomness.
"""
import numpy as np
import sympy
import math

def subgroup_indicator(p, n):
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] = 1.0
        x = x * h % p
    return ind

fac = [math.factorial(r) for r in range(0, 20)]

def analyze(p, n, label):
    ind = subgroup_indicator(p, n)
    S = np.fft.fft(ind)
    a2 = np.abs(S) ** 2
    trueB = math.sqrt(float(np.max(a2[1:])))         # exclude b=0
    a2nz = a2.copy(); a2nz[0] = 0.0                  # E_r' excludes b=0 main term
    L = math.log2(p / n); snl = math.sqrt(n * L)
    # c_r at full E_r (with main term) for r up to 11
    cs = []
    for r in range(2, 12):
        Er = float(np.sum(a2 ** r) / p)
        excess = Er - n ** (2 * r) / p
        ratio = excess / (fac[r] * n ** r)
        cs.append(ratio ** (1.0 / r) if ratio > 0 else float('nan'))
    # arrow: min over r of (p * E_r')^{1/2r}
    best = None; bestr = None
    for r in range(1, 14):
        Er2 = float(np.sum(a2nz ** r) / p)
        bnd = (p * Er2) ** (1.0 / (2 * r)) if Er2 > 0 else float('inf')
        if best is None or bnd < best:
            best, bestr = bnd, r
    print(f"{label}")
    print(f"   trueB={trueB:.2f}  sqrt(n*log2(p/n))={snl:.2f}  trueB/sqrt(nL)={trueB/snl:.3f}")
    print(f"   c_r (r=2..11): " + " ".join(f"{c:.3f}" for c in cs))
    print(f"   arrowMin={best:.2f} @r={bestr}  arrow/trueB={best/trueB:.3f}  arrow/sqrt(nL)={best/snl:.3f}")
    return cs

print("=" * 100)
print("DEEP-r + ARROW at the WORST fixed-index prime per n (structured resonance), and a TYPICAL prime.")
print("=" * 100)
# worst primes identified by envelope2 (the structured-resonance picks):
worst = {64: (124, 7937), 128: (512, 65537), 256: (157, 40193), 512: (165, 84481), 1024: (93, 95233)}
for n in (64, 128, 256, 512, 1024):
    m, p = worst[n]
    analyze(p, n, f"n={n}  WORST m={m} p={p}:")
    print()

print("=" * 100)
print("Compare a TYPICAL (median-ish, small index) prime at the same n:")
print("=" * 100)
for n in (256, 512, 1024):
    # first prime at small index
    m = 8
    while True:
        p = m * n + 1
        if p > 200000: break
        if sympy.isprime(p): break
        m += 1
    analyze(p, n, f"n={n}  typical m={m} p={p}:")
    print()

print("READ:")
print("  c_r flat in r (no climb to r=11) at the WORST prime => no deep-moment inflation.")
print("  arrow/trueB and arrow/sqrt(nL) bounded => arrow reaches the true sup ~ sqrt(n log).")
print("  => C bounded in BOTH n and r => the moment arrow is NOT killed by E_r non-randomness.")
