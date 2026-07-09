#!/usr/bin/env python3
"""
C002 fast verdict probe (log-gamma; no giant integers, scales to prize n=2^30).

Claim under attack: the all-witness ownership floor gives a *combinatorial* upper
bound on F3 incidence  I(delta) <= C(n, d+2)/C(w0, d+1),  with NO character-sum input,
and (attack_plan) this should be compared to the prize budget  q*eps* (~ n).

If  C(n,k+1)/C(w0,k) <= q*eps*  in the prize window, the brick alone would CLOSE the prize.
We compute  log2(cap) - log2(budget)  for budget = q*eps* in {n, n^2, n^3, n^5}  (covering
q ~ n^beta tunings, beta in 1..5) across dyadic n up to 2^30 at prize rates rho.

Window for delta = (1 - sqrt(rho),  1 - rho - 1/log n).  We use the BEST (smallest cap)
interior delta = just above Johnson edge => largest w0 => smallest cap. If even there the
cap exceeds the budget, the brick never reaches the prize.
"""
import math
from fractions import Fraction

def lcomb2(a, b):
    # log2 C(a,b) via lgamma
    if b < 0 or b > a or a < 0:
        return float('-inf')
    return (math.lgamma(a+1) - math.lgamma(b+1) - math.lgamma(a-b+1)) / math.log(2)

def best_cap_log2(n, k, delta):
    """log2 of C(n,k+1)/C(w0,k) at the given delta; w0 = floor((1-delta)n) (largest threshold)."""
    w0 = math.floor((1-delta)*n)
    if w0 < k:
        return None, w0
    return lcomb2(n, k+1) - lcomb2(w0, k), w0

def run():
    rhos = [Fraction(1,2), Fraction(1,4), Fraction(1,8), Fraction(1,16)]
    ns = [256, 1024, 4096, 1<<14, 1<<16, 1<<20, 1<<24, 1<<28, 1<<30]
    print("="*108)
    print("C002 verdict probe: log2(cap) - log2(budget) at the EASIEST (smallest-cap) prize-window delta")
    print("  cap = C(n,k+1)/C(w0,k)   (the all-witness floor bound on I(delta))")
    print("  budget = q*eps* for q ~ n^beta * eps*  =>  budget in {n, n^2, n^3, n^5}")
    print("  POSITIVE number = cap exceeds budget by that many bits => brick does NOT reach prize")
    print("="*108)
    print(f"{'n':>10} {'rho':>5} {'k':>10} {'delta_lo':>9} {'w0':>10} {'log2cap':>10} "
          f"{'-log2(n)':>9} {'-log2(n^2)':>10} {'-log2(n^3)':>10} {'-log2(n^5)':>10}")
    for rho in rhos:
        for n in ns:
            kf = rho*n
            if kf.denominator != 1: continue
            k = int(kf)
            if k < 1 or k+1 > n: continue
            johnson = 1 - math.sqrt(float(rho))
            eta = 1.0/max(1.0, math.log(n))
            hi = (1-float(rho)) - eta
            if hi <= johnson: continue
            # smallest cap = delta just above Johnson edge (largest w0)
            delta = johnson + 0.02*(hi-johnson)
            l2cap, w0 = best_cap_log2(n, k, delta)
            if l2cap is None:
                continue
            ln2 = math.log2(n)
            print(f"{n:>10} {str(rho):>5} {k:>10} {delta:>9.4f} {w0:>10} {l2cap:>10.1f} "
                  f"{l2cap-ln2:>9.1f} {l2cap-2*ln2:>10.1f} {l2cap-3*ln2:>10.1f} {l2cap-5*ln2:>10.1f}")
    print()
    print("INTERPRETATION: every entry in the budget columns is hugely POSITIVE (cap >> budget).")
    print("The combinatorial Fisher cap is ~ 2^{Theta(n)} in the prize window, vs budget poly(n).")
    print("So the all-witness floor alone is VACUOUS at the prize; it does NOT supply the missing")
    print("reverse bound that closes I(delta) <= q*eps*. The gap it leaves IS the BGK/analytic wall.")

    # Sanity: reproduce the in-tree concrete payoff (n=16,k=3,d=2,w0=6 => C(16,4)/C(6,3)=91)
    print()
    print("SANITY (in-tree level-1 rung): n=16, d=2 (k=3), w0=6 => C(16,4)/C(6,3) =",
          math.comb(16,4)//math.comb(6,3), "(brick claims 91) ; budget q*eps* needs <= ~31 -> rung stays open, matches docstring")

if __name__ == "__main__":
    run()
