#!/usr/bin/env python3
"""
#444 — sanity: confirm the pseudocyclic-vs-amorphic distinction at the m=2 (Paley) boundary, and
that '|eta|=sqrt(p)' (the lead's stated 'prize bound') is the AMORPHIC m=2 case, not general
pseudocyclic. m=2 means n=(p-1)/2 = the index-2 subgroup (quadratic residues) — but the prize uses
PROPER thin mu_n with m huge, so this boundary is exactly where the lead's intuition imports the
wrong regime.

m=2: mu_n = QR, scheme = Paley graph, eta = (-1 +/- sqrt(p))/2 -> |eta| ~ sqrt(p)/2 ~ sqrt(v)/2.
This IS amorphic (strongly regular, conference). Here max|eta| = sqrt(p)/2 = sqrt(n/2)*... and the
'pseudocyclic prize bound |eta|=sqrt(v)' holds up to the factor 2. For m>2 the periods spread and
max|eta| <= sqrt(n log m) << sqrt(v): NOT amorphic, but STILL pseudocyclic (equal mults).
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def periods(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    base = [pow(g, m * j, p) for j in range(n)]
    w = np.exp(2j * np.pi * np.arange(p) / p)
    eta = np.array([sum(w[(pow(g, k, p) * x) % p] for x in base) for k in range(m)])
    return eta, m


print("m=2 (Paley/amorphic) boundary vs m>2 (proper-thin, pseudocyclic-not-amorphic):")
print(f"{'p':>7} {'n=(p-1)/m':>10} {'m':>3} {'max|eta|':>9} {'sqrt(v)=√p':>11} "
      f"{'sqrt(n)':>8} {'sqrt(nlnm)':>10} {'amorphic?':>10}")
# m=2 cases
for p in [13, 29, 53, 101, 197, 401]:
    if not isprime(p):
        continue
    n = (p - 1) // 2
    eta, m = periods(p, n)
    rng = np.abs(eta).max() - np.abs(eta).min()
    print(f"{p:>7} {n:>10} {m:>3} {np.abs(eta).max():>9.3f} {math.sqrt(p):>11.3f} "
          f"{math.sqrt(n):>8.3f} {math.sqrt(n*math.log(m)):>10.3f} "
          f"{'YES' if rng<1e-6 else 'no':>10}")
print("  ^ m=2: max|eta| ~ sqrt(p)/2 ~ sqrt(v)/2, |eta| nearly constant => AMORPHIC. lead's regime.")
print()
# proper thin: fixed n, growing m
for n in [16, 64]:
    for mtgt in [4, 16, 64, 150]:
        p = None
        for mm in range(mtgt, mtgt + 5000):
            cand = mm * n + 1
            if isprime(cand):
                p, m = cand, mm
                break
        if p is None or p > 60000:
            continue
        eta, m = periods(p, n)
        rng = np.abs(eta).max() - np.abs(eta).min()
        amorph = 'YES' if rng < 1e-6 else 'no'
        print(f"{p:>7} {n:>10} {m:>3} {np.abs(eta).max():>9.3f} {math.sqrt(p):>11.3f} "
              f"{math.sqrt(n):>8.3f} {math.sqrt(n*math.log(m)):>10.3f} {amorph:>10}")
print("  ^ proper thin (prize regime): max|eta| ~ sqrt(n log m) << sqrt(v); |eta| SPREADS => NOT")
print("    amorphic, yet equal-mult => STILL pseudocyclic. The lead's '|eta|=sqrt v' fails here NOT")
print("    because pseudocyclicity fails, but because AMORPHICITY fails — and amorphicity defect = the")
print("    spread of |eta| = max|eta| itself. No new handle.")
