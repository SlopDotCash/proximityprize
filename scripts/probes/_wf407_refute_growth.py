#!/usr/bin/env python3
"""
#407 REFUTATION pt3 — the PRIZE-DIAGONAL growth test.

The prize regime holds the INDEX m = (p-1)/n ~ 2^128 (LARGE, ~constant) while
n = 2^mu grows. The conjecture B <= C sqrt(n ln m) then says: with ln m ~ const,
B/sqrt(n) <= C sqrt(ln m) ~ const, i.e. R = B/sqrt(n ln m) stays bounded as n grows.

We can't reach m=2^128, but we CAN hold m in a FIXED band (a few hundred / few
thousand) and grow n = 2^mu, taking the WORST (max over many primes) R at each
(n, m-band). If worst-R TRENDS UP with n at fixed m-band, the conjecture is in
trouble; if it saturates, it holds. We sweep several m-bands.

For each n=2^mu and each m in a band, p = n*m+1 if prime; B exact via coset scan.
worst-R(n, band) = max over all such primes.
"""
import math
import numpy as np
from sympy import isprime, primitive_root

P = lambda *a, **k: print(*a, flush=True, **k)

def floor_B(p, n, g=None):
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64); cur = 1
    for k in range(n): mu[k] = cur; cur = cur*gm % p
    tp = 2.0*math.pi/p
    best = 0.0; r = 1
    for _ in range(m):
        pr = (r*mu) % p
        s = np.cos(tp*pr).sum() + 1j*np.sin(tp*pr).sum()
        a = abs(s)
        if a > best: best = a
        r = r*g % p
    return best

P("="*78)
P("REFUTATION pt3 — prize-diagonal growth: worst R(n) at FIXED m-band")
P("="*78)
P("  conjecture holds  <=> worst-R stays bounded as n grows at fixed m-band")

# m-bands chosen so p = n*m stays <= ~6e6 even for the largest n.
# band -> (mlo, mhi)
bands = {
    "m in [16,32)":   (16,32),
    "m in [32,64)":   (32,64),
    "m in [64,128)":  (64,128),
    "m in [128,256)": (128,256),
}
ns = [8,16,32,64,128,256,512,1024]

for label,(mlo,mhi) in bands.items():
    P(f"\n--- {label} ---")
    P(f"  {'n':>6} {'worstR':>8} {'B':>10} {'p':>9} {'m':>6} {'shallow':>8} {'#primes':>8} {'medR':>7}")
    prev = None
    for n in ns:
        if n*mhi > 6_500_000:   # compute cap
            P(f"  {n:>6}  (skipped: p too large for exact scan)")
            continue
        Rs = []
        best = None
        for m in range(mlo, mhi):
            p = n*m + 1
            if not isprime(p): continue
            g = primitive_root(p)
            B = floor_B(p, n, g)
            R = B/math.sqrt(n*math.log(m))
            Rs.append(R)
            if best is None or R > best[0]:
                best = (R,B,p,m,p/n**2.5)
        if not Rs:
            P(f"  {n:>6}  (no primes in band)"); continue
        Rs.sort()
        med = Rs[len(Rs)//2]
        R,B,p,m,sh = best
        arrow = ""
        if prev is not None:
            arrow = " UP" if R > prev+0.01 else (" dn" if R < prev-0.01 else " ~")
        prev = R
        P(f"  {n:>6} {R:8.4f} {B:>10.3f} {p:>9} {m:>6} {sh:>8.2f} {len(Rs):>8} {med:>7.4f}{arrow}")

P("\n--- VERDICT LOGIC ---")
P("  If worstR climbs monotonically with n in a band -> floor refuted (C grows).")
P("  If worstR saturates/oscillates around a ceiling -> floor supported (C bounded).")
P("\nDONE pt3.")
