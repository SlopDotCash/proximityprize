#!/usr/bin/env python3
"""
#407 route-unification: measure the EXACT two-way tightness between
  (analytic)  B = max_{b!=0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x)
  (energy/NVM) E_r = #{ (x,y) in mu_n^{2r} : sum x = sum y  (mod p) }
linked by the in-tree moment arrow and its EXACT identity:
      q * E_r  =  sum_{b in F_p} |eta_b|^{2r}        (Parseval / orthogonality)
      n^{2r}   =  the b=0 term (|eta_0| = n)
  => q*E_r - n^{2r} = sum_{b!=0} |eta_b|^{2r}.

FORWARD  (energy => sup-norm):   B^{2r} <= sum_{b!=0}|eta_b|^{2r} = q*E_r - n^{2r}
                                 => B <= (q*E_r - n^{2r})^{1/2r}     [the moment arrow]
REVERSE  (sup-norm => energy):   sum_{b!=0}|eta_b|^{2r} <= (q-1) * B^{2r}
                                 => q*E_r - n^{2r} <= (q-1) B^{2r}.

The question (route-unification, slack hunt): how lossy is each arrow at the
OPTIMAL r ~ ln m?  If the FORWARD arrow at optimal r already recovers B up to a
constant, then "energy/NVM bound" and "sup-norm bound" are the SAME object (no
slack to exploit).  We measure, at each r, the ratio
      forward_pred(r) / B_true     (>=1; how much the moment arrow over-estimates B)
and the reverse efficiency
      (q*E_r - n^{2r}) / ((q-1) B^{2r})   (<=1; how much of the L^{2r} mass the max carries)
at the r that MINIMIZES forward_pred -- that is the operative r for the prize floor.
"""
import math, cmath
from sympy import isprime, primitive_root

def gauss_periods(p, n):
    g = primitive_root(p)                       # generator of F_p^*
    # mu_n = order-n subgroup = { g^{m*k} : k } where m = (p-1)/n
    m = (p - 1) // n
    base = pow(g, m, p)
    H = [pow(base, k, p) for k in range(n)]      # the subgroup mu_n
    assert len(set(H)) == n
    w = 2j * math.pi / p
    etas = []
    for b in range(p):
        s = sum(cmath.exp(w * ((b * x) % p)) for x in H)
        etas.append(s)
    return etas, m

def analyze(p, n):
    etas, m = gauss_periods(p, n)
    abs2 = [abs(e)**2 for e in etas]             # |eta_b|^2
    n0 = abs2[0]                                  # = n^2 (b=0)
    assert abs(n0 - n*n) < 1e-6, (n0, n*n)
    nz = abs2[1:]                                 # b != 0
    B = math.sqrt(max(nz))                        # the prize floor B
    rms = math.sqrt(sum(nz)/(p-1))               # Parseval RMS = sqrt(n)
    lnm = math.log(m)
    print(f"p={p} n={n} m={m} beta=log_n(p)={math.log(p)/math.log(n):.3f}")
    print(f"  B={B:.4f}  RMS={rms:.4f}(=sqrt(n)={math.sqrt(n):.4f})  B/sqrt(n)={B/math.sqrt(n):.3f}"
          f"  B/sqrt(n ln m)={B/math.sqrt(n*lnm):.3f}")
    rows = []
    best = None
    for r in range(1, 60):
        # exact sum_{b!=0} |eta_b|^{2r}  (= q*E_r - n^{2r})
        S = sum(a**r for a in nz)
        fwd = S ** (1.0/(2*r))                    # moment-arrow prediction for B
        # reverse efficiency: fraction of L^{2r} mass the max carries
        rev_eff = S / ((p-1) * (B**(2*r)))        # in (0,1]; ->1 iff max dominates
        rows.append((r, fwd, fwd/B, rev_eff))
        if best is None or fwd < best[1]:
            best = (r, fwd, fwd/B, rev_eff)
    # report the operative r* (minimizer of the forward prediction)
    r_star, fwd_star, over_star, rev_star = best
    print(f"  optimal r* (min moment-arrow pred) = {r_star},  ln m = {lnm:.2f}")
    print(f"  FORWARD  at r*: pred={fwd_star:.4f}  pred/B_true={over_star:.3f}  (1.0 = tight)")
    print(f"  REVERSE  at r*: L^2r mass fraction carried by max = {rev_star:.4e}")
    # also show a few representative r
    print("   r |  fwd_pred  fwd/B   rev_eff")
    for r, fwd, over, rev in rows:
        if r in (1,2,3,5,8,r_star) or r==rows[-1][0]:
            print(f"  {r:2d} | {fwd:8.4f}  {over:5.3f}  {rev:.3e}")
    return over_star

# prime-field, p == 1 mod n, dyadic n, modest m so brute force is feasible.
# choose primes with p-1 = n*m, n=2^mu, growing m, all <~ 6e4.
cases = [
    (193,  16),   # p-1=192=16*12
    (257,  16),   # 256=16*16
    (1409, 64),   # 1408=64*22
    (3329, 256),  # 3328=256*13   (a real NTT prime!)
    (12289, 256), # 12288=256*48  (Falcon/NTT prime)
    (40961, 4096),# 40960=4096*10 (NTT prime)
]
overs = []
for p, n in cases:
    assert isprime(p) and (p-1) % n == 0
    overs.append(analyze(p, n))
    print()
print("FORWARD arrow over-estimate factor (pred/B at optimal r) across cases:",
      [f"{o:.3f}" for o in overs])
print("=> if these are bounded O(1) and flat, the moment/NVM bound and the sup-norm B")
print("   are the SAME object up to a constant: no slack to exploit by switching routes.")
