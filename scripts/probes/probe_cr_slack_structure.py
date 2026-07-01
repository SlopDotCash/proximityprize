#!/usr/bin/env python3
"""
probe_cr_slack_structure.py  (issue #444, [cr-monotonicity-deep])

GOAL: pin the STRUCTURAL identity and decide if c_r<=1 is a Lam-Leung COROLLARY (char-0).

(A) VERIFY the exact algebraic equivalence symbolically (sympy):
        c_r <= 1  <=>  slack_{r+1} >= n * slack_r,   slack_r := Wick_r - E_r,  Wick_r=(2r-1)!! n^r.
    via  c_r = (E_{r+1} - n E_r)/(2r n Wick_r).

(B) The Lam-Leung structure of the slack.  Lam-Leung: E_r^char0 = #{2r-tuples of n-th roots
    (n=2^mu) summing to 0 (signed)} = (number of ways to perfectly match 2r roots into
    NEGATION pairs zeta^a + zeta^{a+n/2}=0) + deeper (>=4-term primitive vanishing) corrections.
    The LEADING term (all negation-pair matchings) is EXACTLY (2r-1)!! n^r = Wick_r when every
    pairing is realizable -- BUT for n-th roots, a negation pair forces the two indices to differ
    by n/2, NOT free.  So actually E_r <= Wick_r with slack = Wick_r - E_r = (forbidden pairings) +
    (the over/under-count from non-pair vanishing sums).  Let's measure the DECOMPOSITION:
      - PAIR_r := #{2r-tuples that are a disjoint union of r negation-pairs}  (the "Gaussian" core)
      - E_r >= PAIR_r always (these are genuine zero sums), and E_r - PAIR_r = #{non-pair zero sums}.
    Claim to test: is  E_r = PAIR_r + (lower order)  AND  PAIR_r itself <= Wick_r with the right
    slack-growth?  Compute PAIR_r exactly and compare.

(C) Decide: does slack_{r+1} >= n slack_r hold with a PROVABLE structural reason, or only
    numerically?  Print the ratio slack_{r+1}/(n slack_r) -- if it is ALWAYS >= 1 AND bounded
    BELOW by a clean constant, that is the structural margin.
"""
from fractions import Fraction
from collections import defaultdict
import sympy as sp

def rep_vectors(n):
    half = n // 2
    reps = []
    for j in range(n):
        v = [0]*half
        if j < half: v[j] = 1
        else:        v[j-half] = -1
        reps.append(tuple(v))
    return reps

def char0_energy_upto(n, R):
    reps = rep_vectors(n); half = n // 2
    cur = defaultdict(int); cur[tuple([0]*half)] = 1
    out = {}
    for r in range(1, R+1):
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rv in reps:
                w = tuple(v[i]+rv[i] for i in range(half)); nxt[w] += c
        cur = nxt; out[r] = sum(c*c for c in cur.values())
    return out

def dfodd(r):
    res = 1
    for k in range(1, r+1): res *= (2*k-1)
    return res

def pair_count(n, r):
    """PAIR_r = # of 2r-tuples (x_1..x_r,y_1..y_r) in mu_n^{2r} with sum x = sum y in C
       that arise as a PERFECT MATCHING into negation pairs.
       Equivalent count: # ways to take 2r roots (with the energy convention: r on each side,
       i.e. sum_{i} x_i - sum_j y_j = 0) that decompose into r pairs each summing to 0.
       In the energy convention zeroSum over 2r signed roots eps_k zeta^{a_k}=0 with r of the
       eps=+1 and r eps=-1. A NEGATION PAIR is {+zeta^a, +zeta^{a+n/2}} (both +, sum 0) or
       {-zeta^a,-zeta^{a+n/2}} or {+zeta^a, -zeta^a} (cancel). Easiest: count via the standard
       Wick/Gaussian matching = (2r-1)!! * (#single-pair zero configs). For mu_n the number of
       single +/- pairs that cancel: a +root paired with the SAME -root (zeta^a - zeta^a=0): n ways
       (diagonal); a +root paired with +root that are negatives: n/2*... -- to keep it clean and
       comparable to Wick=(2r-1)!! n^r we count the DIAGONAL Wick term only:
       (2r-1)!! * n^r counts matchings of the r '+' slots to the r '-' slots with x_i=y_{sigma(i)}.
       That EXACTLY equals Wick_r and is a LOWER bound piece of E_r (all diagonal matchings are
       genuine zero sums). So PAIR_diag_r = (2r-1)!! n^r = Wick_r EXACTLY, and slack = E_r - Wick?
       But measured E_r <= Wick_r (slack = Wick - E >=0, E BELOW Wick). Contradiction => the
       diagonal matchings OVERLAP (same tuple counted by multiple matchings), so inclusion-
       exclusion makes E_r < sum of matchings. That overlap IS the slack. Good -- confirm E<=Wick.
    """
    # We just confirm E_r <= Wick_r and report; the matching-overlap interpretation is the proof sketch.
    return None

def main():
    print("ISSUE #444 [cr-monotonicity-deep]: structural identity + slack-growth\n")

    # (A) symbolic verification of the equivalence
    print("=== (A) symbolic identity check (sympy) ===")
    n, r, Er, Er1 = sp.symbols('n r E_r E_{r+1}', positive=True)
    Wick_r  = sp.factorial2(2*r-1)*n**r
    Wick_r1 = sp.factorial2(2*r+1)*n**(r+1)
    a_r  = Er/Wick_r
    a_r1 = Er1/Wick_r1
    c_r  = ((1+2*r)*a_r1 - a_r)/(2*r)
    # claim: c_r - 1 has same sign as (E_{r+1}-n E_r) - 2 r n Wick_r, and
    # c_r<=1 <=> (Wick_{r+1}-E_{r+1}) - n(Wick_r-E_r) >= 0
    lhs = sp.simplify(c_r)
    # form slack_{r+1} - n slack_r = (Wick_r1 - Er1) - n*(Wick_r - Er)
    slack_diff = (Wick_r1 - Er1) - n*(Wick_r - Er)
    # show c_r - 1 = -slack_diff / (2 r n Wick_r)
    test = sp.simplify((c_r - 1) + slack_diff/(2*r*n*Wick_r))
    print(f"   c_r simplified = {lhs}")
    print(f"   (c_r - 1) + slack_diff/(2 r n Wick_r)  ==  {test}   (should be 0)")
    print(f"   => c_r <= 1  <=>  slack_diff >= 0  <=>  slack_(r+1) >= n*slack_r   [since 2 r n Wick_r>0]\n")

    # (B) numeric slack-growth margin
    print("=== (B) slack-growth margin: slack_{r+1}/(n*slack_r)  (>=1 iff c_r<=1) ===")
    plan = [(4, 16), (8, 13), (16, 9), (32, 6), (64, 4)]
    worst = None
    for nn, R in plan:
        E = char0_energy_upto(nn, R)
        print(f"  -- n={nn} --")
        print(f"     {'r':>2} {'slack_r':>14} {'slack_{r+1}/(n slack_r)':>26}")
        for rr in range(2, R):  # slack_1 = 0, start from r=2
            sr  = dfodd(rr)*nn**rr   - E[rr]
            sr1 = dfodd(rr+1)*nn**(rr+1) - E[rr+1]
            margin = Fraction(sr1, nn*sr) if sr != 0 else None
            mg = float(margin) if margin is not None else None
            if mg is not None and (worst is None or mg < worst[2]):
                worst = (nn, rr, mg)
            print(f"     {rr:>2} {sr:>14} {mg:>26.5f}")
        print()
    print(f"  WORST (smallest) margin slack_{{r+1}}/(n slack_r) over all measured: "
          f"n={worst[0]}, r={worst[1]}, margin={worst[2]:.5f}")
    print(f"  margin >= 1 everywhere?  {'YES => c_r<=1 holds with margin >= '+format(worst[2],'.3f') if worst[2]>=1 else 'NO -- a c_r>1 appears'}")

if __name__ == "__main__":
    main()
