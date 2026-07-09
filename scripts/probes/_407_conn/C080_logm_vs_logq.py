"""
C080 follow-up: is the right SCALE sqrt(n log m) (C080) or sqrt(n log q)?  And is the C080
'correct constant sqrt 2' real, or is it just 'correct scale, slack constant'?

Decisive test of the STRUCTURAL claim 'log m not log q':
  At FIXED n, log q = log(m n) = log m + log n.  Since n is fixed and small, log m and log q differ
  only by the additive constant log n. To DISTINGUISH them we vary n WITH m so that log m and log q
  move differently. Sharpest: hold m roughly fixed (the prize regime: m ~ 2^128 fixed, n -> inf),
  vary n; then log m ~ const while log q = log m + log n grows. If B/sqrt(n log m) is flat (no n
  trend) while B/sqrt(n log q) shrinks, that CONFIRMS log m is the structural scale (C080's pin).

We approximate 'm fixed, n growing' by choosing primes with m in a narrow band across several n.
Exact max over all b; proper subgroups; large primes.
"""
import numpy as np
from sympy import isprime, primitive_root
import math

def true_B(p, n):
    g = int(primitive_root(p)); m = (p - 1) // n; gm = pow(g, m, p)
    sub = []; cur = 1
    for _ in range(n):
        sub.append(cur); cur = (cur * gm) % p
    sub = np.array(sub, dtype=np.int64)
    w = np.exp(2j * np.pi * np.arange(p) / p); bs = np.arange(1, p)
    eta = np.zeros(p - 1, dtype=complex)
    for x in sub: eta += w[(bs * x) % p]
    a = np.abs(eta)
    return a.max(), (a ** 2).mean(), m

def prime_with_m_near(n, mtarget):
    """find prime p = m*n+1, m as close to mtarget as possible."""
    best = None
    for dm in range(0, 4000):
        for mm in (mtarget + dm, mtarget - dm):
            if mm < 2: continue
            p = mm * n + 1
            if isprime(p):
                return p, mm
    return None, None

print("=== 'm ~ fixed band, n growing': sqrt(n log m) FLAT vs sqrt(n log q) shrinking? ===")
print("(if log m is the structural scale, B/sqrt(n log m) is flat in n; B/sqrt(n log q) trends down)")
print(f"{'n':>4} {'p':>9} {'m':>7} {'B':>9} {'B/sq(n lnm)':>12} {'B/sq(n lnq)':>12} {'B/(2sqn)':>9}")
mtarget = 4096          # hold m near 4096 across n = 8,16,32,64,128
for mu in [3, 4, 5, 6, 7]:
    n = 2 ** mu
    p, m = prime_with_m_near(n, mtarget)
    if p is None or p > 1200000:
        print(f"{n:>4}  (skip: prime too large for exact max)")
        continue
    B, meansq, m = true_B(p, n)
    lnm = math.log(m); lnq = math.log(p)
    print(f"{n:>4} {p:>9} {m:>7} {B:>9.3f} {B/math.sqrt(n*lnm):>12.4f} "
          f"{B/math.sqrt(n*lnq):>12.4f} {B/(2*math.sqrt(n)):>9.3f}")

print()
print("=== Constant audit: best-fit C in B = C sqrt(n log m) (proper subgroups, large p) ===")
print("C080 asserts C -> sqrt(2) ~ 1.414. Measured here:")
print(f"{'n':>4} {'p':>9} {'m':>8} {'C=B/sq(n lnm)':>14}")
for (mu, betas) in [(3,[4.0,4.5,5.0]),(4,[4.0,4.5]),(5,[3.5,4.0])]:
    n = 2**mu
    for beta in betas:
        target = int(round(n**beta))
        if target > 1100000: continue
        p = target - (target % n) + 1
        while not (p>n and isprime(p)): p += n
        if p>1200000: continue
        B, meansq, m = true_B(p, n)
        print(f"{n:>4} {p:>9} {m:>8} {B/math.sqrt(n*math.log(m)):>14.4f}")
