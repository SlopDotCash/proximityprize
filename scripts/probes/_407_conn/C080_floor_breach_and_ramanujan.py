"""
C080 decisive checks:
 (A) Does B ever EXCEED the EVT floor sqrt(2 n log m)?  (If yes, the floor is NOT even an upper bound,
     so it cannot be 'the target B <= C sqrt(n log m)' with C=sqrt2; the EVT step is heuristic only.)
 (B) Robustness of 'Ramanujan 2 sqrt(n) is FALSE in regime': scan many proper-subgroup primes,
     report max B/(2 sqrt n) and whether it is ALWAYS > 1 (Ramanujan breached) and growing in m.
 (C) Which i.i.d. EVT MODEL matches?  max of m iid Rayleigh(scale sigma, E|.|^2=2sigma^2=n) ->
     sigma sqrt(2 ln m) = sqrt(n ln m)  [constant 1, NOT sqrt2].
     The sqrt2 in 'sqrt(2 n ln m)' corresponds to max of m iid REAL N(0,n) -> sqrt(2 n ln m).
     The periods are COMPLEX (variance n split over re/im), so the Rayleigh model (constant 1) is the
     right i.i.d. null, and the data should hug C ~ 1 (mildly above due to correlation), NOT sqrt2.
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
    return a.max(), m

print("=== (A) breach of floor sqrt(2 n log m) and (B) Ramanujan robustness, many proper primes ===")
print(f"{'n':>4} {'p':>9} {'m':>7} {'B':>9} {'B/(2sqn)':>9} {'B/sq(2nlnm)':>12} {'breach?':>8}")
any_breach = False
ramanujan_min = 99.0
for mu in [3, 4, 5]:
    n = 2 ** mu
    cnt = 0
    p = max(2 * n, int(n ** 3.4))
    while cnt < 6 and p < 800000:
        p += 1
        if p % n != 1:  # need p = 1 mod n
            p += (n - (p % n) + 1) % n
            if (p - 1) % n != 0:
                continue
        if not isprime(p):
            continue
        B, m = true_B(p, n)
        if m < 50:  # keep it a proper, large-index subgroup
            continue
        twosqn = 2 * math.sqrt(n)
        floor = math.sqrt(2 * n * math.log(m))
        breach = B > floor
        any_breach = any_breach or breach
        ramanujan_min = min(ramanujan_min, B / twosqn)
        print(f"{n:>4} {p:>9} {m:>7} {B:>9.3f} {B/twosqn:>9.3f} {B/floor:>12.4f} {str(breach):>8}")
        cnt += 1
        p = int(p * 1.7)

print()
print(f"ANY floor breach (B > sqrt(2 n log m))? {any_breach}")
print(f"MIN B/(2 sqrt n) over all proper-subgroup rows: {ramanujan_min:.3f}  "
      f"(>1 everywhere => Ramanujan cap 2sqrt(n) breached at EVERY tested config)")
print()
print("=== (C) i.i.d. null model identification: C = B/sqrt(n ln m) should hug ~1 (Rayleigh), not sqrt2 ===")
Cs = []
for mu in [3,4,5]:
    n = 2**mu
    for beta in [3.6, 4.0, 4.4]:
        target = int(round(n**beta))
        if target > 900000: continue
        p = target - (target % n) + 1
        while not (p>n and isprime(p)): p += n
        if p>1000000: continue
        B, m = true_B(p, n)
        C = B/math.sqrt(n*math.log(m))
        Cs.append(C)
print(f"  measured C list: {[round(c,3) for c in Cs]}")
print(f"  mean C = {np.mean(Cs):.3f}  (Rayleigh i.i.d. null = 1.000 ; C080's sqrt2 = {math.sqrt(2):.3f})")
print(f"  => the i.i.d. extreme-value SCALE sqrt(n log m) is right; the sqrt2 CONSTANT is not the limit.")
