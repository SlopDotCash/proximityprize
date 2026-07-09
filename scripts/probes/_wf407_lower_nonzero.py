#!/usr/bin/env python3
"""
WF407 / lowerbound — the CORRECT nonzero-b moment-ratio bound.

The max over ALL b is trivially won by b=0 (eta_0 = n, |eta_0|^2 = n^2). The PRIZE object is
   B^2 = max_{b != 0} |eta_b|^2.
The correct moment-ratio lower bound must SUBTRACT the b=0 spike from BOTH moments:
   sum_{b!=0} |eta_b|^2 = q*n - n^2          =: S2
   sum_{b!=0} |eta_b|^4 = q*E - n^4          =: S4
Then  B^2 = max_{b!=0} |eta_b|^2 >= S4 / S2   (since S4 = sum |eta|^2 |eta|^2 <= B^2 * S2).
   =>  B^2 >= (q*E - n^4) / (q*n - n^2) = (q*E - n^4) / (n(q - n)).
This is the EXACT, provable nonzero-b lower bound. Test it holds, and what constant it gives.

Also test the AVERAGE-over-nonzero-cosets bound L0':
   B^2 >= S2/(p-1) = (q n - n^2)/(p-1) = n(q-n)/(q-1) ~ n   (the bare sqrt(n) floor, nonzero).
"""
import cmath, math
from collections import Counter

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = []; t = phi; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t //= d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac): return g

def data(p, n):
    g = primitive_root(p); m = (p-1)//n
    gen = pow(g, m, p); mu = []; x = 1
    for _ in range(n): mu.append(x); x = (x*gen) % p
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    B2 = 0.0; bc = 1
    for _ in range(m):
        s = 0j
        for xx in mu: s += e[(bc*xx) % p]
        B2 = max(B2, abs(s)**2); bc = (bc*g) % p
    cnt = Counter()
    for a in mu:
        for b in mu: cnt[(a+b) % p] += 1
    E = sum(v*v for v in cnt.values())
    return B2, E, m

print("CORRECT nonzero-b lower bounds (subtract the b=0 spike):")
print("  L0' = (q n - n^2)/(p-1)        [2nd-moment avg, ~ n]")
print("  L1' = (q E - n^4)/(q n - n^2)  [4th/2nd moment ratio, nonzero]")
print(f"{'n':>4} {'p':>8} {'m':>6} | {'B^2':>9} {'L0p':>8} {'L1p':>9} | {'L1p/n':>6} "
      f"{'B/√L1p':>7} {'√logm':>6}  hold?")
allok = True
for n in [8,16,32,64,128]:
    p = n+1; rows = 0
    while rows < 5:
        p += n
        if p > 300000: break
        if is_prime(p) and (p-1)%n==0:
            m = (p-1)//n
            if m < 16: continue
            q = p
            B2, E, m = data(p, n)
            S2 = q*n - n*n
            S4 = q*E - n**4
            L0p = S2/(p-1)
            L1p = S4/S2
            hold = (L0p <= B2 + 1e-6) and (L1p <= B2 + 1e-6)
            allok = allok and hold
            print(f"{n:>4} {p:>8} {m:>6} | {B2:9.2f} {L0p:8.3f} {L1p:9.3f} | {L1p/n:6.3f} "
                  f"{math.sqrt(B2/L1p):7.3f} {math.sqrt(math.log(m)):6.3f}  {hold}")
            rows += 1
print(f"\nALL nonzero-b bounds hold: {allok}")
print("L1p/n = the multiplier of n the 4th/2nd nonzero ratio delivers (the provable constant^2).")
print("B/sqrt(L1p) = the residual gap = the missing sqrt(log m) factor.")
