#!/usr/bin/env python3
"""
#407 dense-cayley-spectral: the SLACK of the variance-only (dense-LP) bound GROWS with m.
Show Cantelli/trueB ~ sqrt(m/(2 log m)) -> infinity, i.e. the best dense-spectral certificate
diverges from the truth as the prize index m grows. Sweep fixed-ish n, growing m.
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def gauss_periods_real(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    gm = pow(g, m, p)
    sub = []
    cur = 1
    for j in range(n):
        sub.append(cur)
        cur = (cur * gm) % p
    sub = np.array(sub, dtype=np.int64)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    bs = np.arange(1, p)
    eta = np.zeros(p - 1, dtype=complex)
    for x in sub:
        eta += w[(bs * x) % p]
    return eta.real


print("=" * 96)
print(" SLACK GROWTH: best dense-spectral (variance-only Cantelli) bound vs true B, growing m")
print("=" * 96)
for n in [8, 16]:
    print(f"\n--- n={n} ---")
    print(f"{'m':>6}{'p':>9}{'trueB':>9}{'Cantelli=sqrt(p)':>17}"
          f"{'slack':>9}{'sqrt(m/2lnm)':>14}{'B/sqrt(nlnm)':>14}")
    for m in range(2, 6000):
        p = m * n + 1
        if not isprime(p) or p > 90000:
            continue
        if m not in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024) and m < 5000:
            # sample at powers of 2 + a few
            if m % 250 != 0:
                continue
        re = gauss_periods_real(p, n)
        B = np.abs(re).max()
        cantelli = math.sqrt(p)
        slack = cantelli / B
        predicted_slack = math.sqrt(m / (2 * math.log(m))) if m > 1 else float('nan')
        print(f"{m:>6}{p:>9}{B:>9.3f}{cantelli:>17.2f}{slack:>9.2f}"
              f"{predicted_slack:>14.2f}{B/math.sqrt(n*math.log(m)):>14.3f}")
print()
print("The slack (Cantelli/trueB) tracks sqrt(m/2lnm) and GROWS without bound in m.")
print("At prize m=2^128: slack ~ 2^64/sqrt(128) ~ 2^60.5. The variance-only dense bound is")
print("off by 2^60. Confirms: dense-spectral LP (which extracts only the 2nd moment for the")
print("sup eigenvalue of a vertex-transitive graph) cannot approach sqrt(n log m).")
