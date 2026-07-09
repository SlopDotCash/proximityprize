#!/usr/bin/env python3
"""
#407 unification, part 2: does the FORWARD-arrow over-estimate stay O(1) as ln m grows,
and does the operative r* TRACK ln m?  This is the decisive test of whether the
NVM/energy route and the analytic sup-norm route are the SAME wall asymptotically.

We use larger m (so ln m is larger) and an uncapped r search.  We report:
  - r* = argmin_r (sum_{b!=0}|eta_b|^{2r})^{1/2r}  (the operative moment depth)
  - over* = pred(r*)/B   (the forward over-estimate)
  - and whether r* ~ c * ln m  (the predicted optimal depth).
If over* stays ~1 and r* ~ ln m, the two routes are one wall.  Any DRIFT UP in over*
with ln m would be exploitable slack (the NVM route could be strictly easier).
"""
import math, cmath
from sympy import isprime, primitive_root

def gauss_periods(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    base = pow(g, m, p)
    H = [pow(base, k, p) for k in range(n)]
    assert len(set(H)) == n
    w = 2j * math.pi / p
    return [sum(cmath.exp(w * ((b * x) % p)) for x in H) for b in range(p)], m

def analyze(p, n, rmax=300):
    etas, m = gauss_periods(p, n)
    nz = [abs(e)**2 for e in etas[1:]]
    Bsq = max(nz)
    B = math.sqrt(Bsq)
    lnm = math.log(m)
    # normalize: a_i = |eta|^2 / Bsq in (0,1]; sum a_i^r = S / Bsq^r,
    # so fwd = S^{1/2r} = B * (sum a_i^r)^{1/2r}.  No overflow.
    norm = [a / Bsq for a in nz]
    best = None
    for r in range(1, rmax+1):
        Sn = sum(a**r for a in norm)             # >= 1 (max term contributes 1)
        fwd = B * (Sn ** (1.0/(2*r)))
        if best is None or fwd < best[1]:
            best = (r, fwd)
    r_star, fwd_star = best
    over = fwd_star / B
    capped = (r_star == rmax)
    print(f"p={p:6d} n={n:5d} m={m:6d} ln m={lnm:5.2f} | B={B:8.3f} "
          f"B/sqrt(n ln m)={B/math.sqrt(n*lnm):.3f} | r*={r_star:3d}{'(CAP)' if capped else ''} "
          f"r*/ln m={r_star/lnm:5.2f} | pred/B={over:.4f}")
    return over, r_star, lnm, capped

# primes with LARGER m (index), modest n, p feasible for brute force (<~ 3e5).
# p-1 = n*m, n=2^mu.
cases = [
    (7681,   256),   # 7680 = 256*30
    (12289,  256),   # 12288 = 256*48
    (40961,  256),   # 40960 = 256*160   <- big m
    (61441,  4096),  # 61440 = 4096*15
    (163841, 4096),  # 163840 = 4096*40
    (786433, 256),   # 786432 = 256*3072 <- very big m (3072), n small
    (5767169,256),   # 5767168 = 256*22528 huge m  (may be slow)
]
res = []
for p, n in cases:
    if not (isprime(p) and (p-1) % n == 0):
        print(f"skip p={p} n={n} (not prime or n nmid)"); continue
    if p > 1_200_000:
        print(f"skip p={p} (too large for brute force here)"); continue
    res.append(analyze(p, n))
print()
print("over* (pred/B at optimal r) vs ln m:")
for over, rstar, lnm, cap in res:
    print(f"  ln m={lnm:5.2f}: over*={over:.4f} {'[r capped-untrustworthy]' if cap else ''}")
print("VERDICT: over* flat & ~1 across growing ln m => one wall (energy<->sup-norm tight).")
