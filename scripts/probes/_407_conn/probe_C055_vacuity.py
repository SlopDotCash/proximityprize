#!/usr/bin/env python3
"""
C055 probe: "The proven tau-lower bound IS the s=1 vacuity wall."

We verify, with exact integer/rational arithmetic, the two ARITHMETIC claims of C055:

 (1) Consumer feasibility.  subspaceDesign_list_card_le needs the hypothesis
        hbig :  tau(r)*n + r*n < (r+1)*a       (a = agreement, a <= n always)
     With the FRS profile  tau(r) = (k-1)/n on [s]={1..s},  tau(r) = 1 off [s].
     CLAIM: for s = 1 (plain Reed-Solomon, block alphabet F^1) and any working rank
     r >= 2, the design is OFF range, tau(r) = 1, and hbig is UNSATISFIABLE because it
     forces a > n.

 (2) Schubert-denominator coincidence.  BCDZ25 Thm 1.11 cites vacuity via the
     denominator (s - d + 1) (d = "design rank" argument).  CLAIM: the [s]-range
     cutoff r in {1..s} is exactly the locus where that denominator is positive,
     i.e. the off-[s] collapse (r > s) is the same boundary as (s - r + 1) <= 0.

This is a *consistency / arithmetic* probe.  It does NOT touch the BGK / Paley
sqrt-cancellation core; C055 is a statement ABOUT the in-tree machine-checked
dichotomy, not a route into the analytic prize core.
"""

from fractions import Fraction as Fr

def tau(r, k, s, n):
    """FRS profile per frs_is_subspaceDesign_gk16: (k-1)/n on [s], else 1."""
    if 1 <= r <= s:
        return Fr(k - 1, n)
    return Fr(1, 1)

def hbig_satisfiable(r, k, s, n):
    """Is there an integer agreement a with 1 <= a <= n satisfying
       tau(r)*n + r*n < (r+1)*a ?  (a <= n is forced: at most n coordinates.)
       Return (satisfiable, min_a_needed) where min_a_needed is the strict
       threshold a must EXCEED, as a Fraction."""
    t = tau(r, k, s, n)
    lhs = t * n + r * n            # tau(r)*n + r*n
    # need (r+1)*a > lhs  =>  a > lhs/(r+1)
    thresh = lhs / (r + 1)
    # smallest integer a with a > thresh:
    import math
    a_min = math.floor(thresh) + 1
    feasible = a_min <= n
    return feasible, thresh, a_min

print("=" * 78)
print("CLAIM (1): s=1 plain RS, working rank r>=2 -> hbig forces a>n (UNSAT).")
print("=" * 78)
print(f"{'s':>3}{'r':>3}{'k':>4}{'n':>5} | {'tau(r)':>8} | {'thresh a>':>12} | {'a<=n?':>6} | feasible")
print("-" * 78)
all_s1_r2_unsat = True
# plain RS: s=1.  RS over F_q, length n, dimension k.  Try several (k,n).
for (k, n) in [(2, 8), (4, 16), (8, 32), (16, 64), (33, 64), (4, 8), (2, 4)]:
    s = 1
    for r in [1, 2, 3, 4]:
        feas, thresh, a_min = hbig_satisfiable(r, k, s, n)
        t = tau(r, k, s, n)
        flag = "FEAS" if feas else "UNSAT"
        print(f"{s:>3}{r:>3}{k:>4}{n:>5} | {str(t):>8} | a>{float(thresh):>9.3f} | {str(a_min<=n):>6} | {flag}")
        if s == 1 and r >= 2 and feas:
            all_s1_r2_unsat = False
print()
print(f"  --> for s=1, EVERY r>=2 row is UNSAT (a>n required): {all_s1_r2_unsat}")
print()

# Direct algebraic check of the off-range collapse, symbolic in n:
# tau(r)=1, r>=2:  hbig = n + r*n < (r+1)*a  =>  (r+1)*n < (r+1)*a  =>  n < a.
print("  Algebraic: tau=1 ==> n + r*n = (r+1)*n < (r+1)*a  <=>  n < a.  a<=n ==> false.")
print()

print("=" * 78)
print("CLAIM (2): [s]-range cutoff coincides with Schubert denom (s-r+1) sign flip.")
print("=" * 78)
print(f"{'s':>3}{'r':>3} | {'r in [s]?':>10} | {'(s-r+1)':>8} | {'denom>0?':>9} | match")
print("-" * 78)
coincide = True
for s in [1, 2, 4, 8]:
    for r in range(1, s + 4):
        in_range = (1 <= r <= s)
        denom = s - r + 1
        denom_pos = denom > 0
        # in-range (tau finite, (k-1)/n) iff denom>0 ; off-range (tau=1) iff denom<=0
        m = (in_range == denom_pos)
        if not m:
            coincide = False
        print(f"{s:>3}{r:>3} | {str(in_range):>10} | {denom:>8} | {str(denom_pos):>9} | {'OK' if m else 'MISMATCH'}")
print()
print(f"  --> [s]-range membership == ((s-r+1)>0) for all tested (s,r): {coincide}")
print()
print("=" * 78)
print("VERDICT INPUTS")
print(f"  (1) s=1 r>=2 hbig unsatisfiable everywhere: {all_s1_r2_unsat}")
print(f"  (2) range cutoff == Schubert denom sign:    {coincide}")
print("=" * 78)
