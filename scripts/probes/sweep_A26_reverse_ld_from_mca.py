#!/usr/bin/env python3
"""
sweep_A26_reverse_ld_from_mca.py  --  Actionable A26.

Run the LD<->MCA dictionary BACKWARD: from exact MCA values extract concrete
beyond-Johnson INTERLEAVED list-size lower bounds for explicit smooth-domain RS.

In-tree substrate consumed (all axiom-clean, proven):
  * ReverseDictionary.exists_interleavedList_card_gt_of_epsMCA_gt :
        (1 + (n - a)*L)/q < eps_mca(C, delta)  ==>  EXISTS pair, L < |interleavedList(C, f1, f2, a)|
        where  a = 2*ceil((1-delta)*n) - n   (the "collapse floor").
  * EpsMCAInterleavedJohnson.interleavedList_card_le_johnson :
        |interleavedList(C, f1, f2, a)| <= n^2/(a^2 - n*e)   when  n*e < a^2   (the JOHNSON cap)
        e = pairwise agreement = k-1 for RS.

The BACKWARD extraction:
  Take an EXACT eps_mca value.  Pick L = the Johnson interleaved cap L_J(a) = n^2/(a^2 - n*e)
  (the list size the literature's Johnson bound predicts as a CEILING).
  If  (1 + (n-a)*L_J(a))/q < eps_mca(C, delta)  then the reverse dictionary forces
  EXISTS pair with interleaved list > L_J(a)  ==>  the pair's interleaved list provably
  BEATS the Johnson prediction (a beyond-Johnson interleaved list LOWER bound).

CRITICAL CONSISTENCY CHECK (honesty): interleavedList_card_le_johnson is a THEOREM, so a
beyond-Johnson firing is only LOGICALLY POSSIBLE where the Johnson cap does NOT apply, i.e.
where its gap hypothesis  n*e < a^2  FAILS  (a below the Johnson radius a_J = sqrt(n*e)).
A firing inside the gap (n*e < a^2) would be a CONTRADICTION with the proven cap --- so the
probe must verify EVERY firing has  a^2 <= n*e.  (If any firing had n*e<a^2 the substrate
would be inconsistent; we expect zero such.)

We measure, per instance: the collapse floor a, the Johnson radius a_J, where the reverse
dictionary fires, and the magnitude of the beyond-Johnson list lower bound it certifies.
"""

import math
from fractions import Fraction

def ceil_frac(num, den):
    return -((-num) // den)

# ---------------------------------------------------------------------------
# Part 1: re-derive the EXACT MCA / list data for the in-tree F17 instance
# (DeltaStarExactCrossoverF17.lean), independently, by full enumeration.
# This is the strongest in-window EXACT data point: RS[F17, mu_16, k=2], rho=1/8.
# ---------------------------------------------------------------------------

p = 17
G = list(range(1, 17))                     # F^* = mu_16, smooth domain n=16
w = [1,2,3,4,13,15,0,2,16,2,5,8,10,14,1,5] # the in-tree hard word
n = len(G)

def agree(b, c):
    return sum(1 for x, wx in zip(G, w) if (b*x + c) % p == wx)

def listSize(a):
    return sum(1 for b in range(p) for c in range(p) if agree(b, c) >= a)

print("=== Part 1: F17 / mu_16 / k=2 (rho=1/8) exact list sizes (reproduce in-tree decide) ===")
for a in range(0, 9):
    print(f"  listSize(a={a:2d}) = {listSize(a):3d}")
assert listSize(3) == 15, "mismatch vs in-tree listSize_three"
assert listSize(4) == 5,  "mismatch vs in-tree listSize_four"
assert listSize(5) == 3,  "mismatch vs in-tree listSize_five"
print("  [OK] reproduces in-tree listSize_{three,four,five}")

# Johnson radius for the BASE code (single-row, e=k-1=1).
k = 2
e = k - 1
a_J = math.isqrt(n*e)            # Johnson agreement radius floor: largest a with a^2 <= n*e
print(f"  n={n}, k={k}, e=k-1={e}, Johnson radius a_J=floor(sqrt(n*e))=floor(sqrt({n*e}))={a_J}")
print(f"  --> a=3 (<a_J=4) is BELOW the Johnson radius: listSize(3)=15 is a beyond-Johnson")
print(f"      base-code list lower bound; a=4 is exactly the Johnson radius; a>=5 is Johnson-clean.")
print()

# ---------------------------------------------------------------------------
# Part 2: the BACKWARD extraction via the reverse dictionary, on the INTERLEAVED code.
#
# The reverse dictionary uses the collapse floor a_coll = 2*ceil((1-delta)*n) - n,
# i.e. delta enters through t = ceil((1-delta)*n).  We sweep the agreement floor t
# (t = ceil((1-delta)*n) ranges over {0..n}; delta = 1 - t/n) and for each:
#   a_coll = 2*t - n   (only meaningful when 2*t >= n, i.e. delta <= 1/2)
#   Johnson interleaved cap L_J = n^2/(a_coll^2 - n*e)   when  n*e < a_coll^2.
#
# We DO NOT have an exact eps_mca closed value for the interleaved code in Lean for
# this instance, so for the EXTRACTION we use the GENERAL exact lower bound that IS
# in-tree and unconditional:  the reverse dictionary's contrapositive engine.  The
# cleanest fully-rigorous backward statement we can land is the BASE-code list lower
# bound (Part 1) plus the structural fact below; Part 2 quantifies the interleaved
# Johnson cap and where a beyond-Johnson interleaved firing is even LOGICALLY possible.
# ---------------------------------------------------------------------------

print("=== Part 2: interleaved Johnson cap L_J(a_coll) across the collapse-floor sweep ===")
print("  t = ceil((1-delta)*n);  a_coll = 2t-n;  L_J = n^2/(a_coll^2 - n*e) where n*e<a_coll^2")
print(f"  n*e = {n*e}  (Johnson gap requires a_coll^2 > {n*e}, i.e. a_coll >= {a_J+1})")
print(f"  {'t':>3} {'delta':>8} {'a_coll':>7} {'gap?(ne<a^2)':>13} {'L_J=n^2/(a^2-ne)':>18}")
for t in range(n//2, n+1):
    a_coll = 2*t - n
    delta = Fraction(n - t, n)
    if a_coll == 0:
        gap = False
        ljs = "-(a=0)"
    else:
        gap = (n*e < a_coll**2)
        ljs = str(n*n // (a_coll**2 - n*e)) if gap else "INF (a<=a_J: cap N/A)"
    print(f"  {t:>3} {str(delta):>8} {a_coll:>7} {str(gap):>13} {ljs:>18}")
print("  --> WHERE the Johnson interleaved cap is N/A (a_coll <= a_J=4): a_coll in {0,2,4}")
print("      i.e. t in {8,9,10}  (delta in {1/2, 7/16, 3/8}).  ONLY there can a beyond-Johnson")
print("      interleaved list lower bound be logically consistent with the proven cap.")
print()

# ---------------------------------------------------------------------------
# Part 3: the firing condition for the reverse dictionary, prize-shaped.
#
# Reverse dictionary fires (forces interleaved list > L) iff:
#       (1 + (n - a_coll)*L)/q  <  eps_mca(C, delta).
# To CERTIFY a beyond-Johnson lower bound we must (i) be at a_coll <= a_J (cap N/A), and
# (ii) have an exact eps_mca value exceeding (1 + (n-a_coll)*L)/q for L = (Johnson-radius
# list size).  The largest exact in-tree eps_mca values are the explosion-band values
# eps_mca up to ~ (a_coll-clustered list)/q.  We test the SELF-CONSISTENT firing using the
# base-code exact list size as the eps_mca driver (eps_mca >= #badscalars/q, and the
# far-coset law gives eps_mca = (clustered list)/q at explosion).
# ---------------------------------------------------------------------------

print("=== Part 3: reverse-dictionary firing test (prize-shaped q) ===")
# At the collapse floor a_coll, the interleaved list of a SPLIT stack (u0,u1)=(line0,line1)
# realizes >= listSize(t)_per_row clustering.  We use the exact base list sizes as a proxy
# eps driver and ask: for which L does (1+(n-a_coll)*L)/q < L/q  hold => forces list>L.
# Note (1+(n-a)*L)/q < (list)/q  <=>  1+(n-a)*L < list.  This is the clean integer firing.
for label, q in [("F17 (q=17)", 17), ("prize q~n*2^128", n * 2**128)]:
    print(f"  -- {label} --")
    for t in [10, 9, 8]:           # the a_coll <= a_J rows where beyond-Johnson is possible
        a_coll = 2*t - n
        # exact base list size at this agreement floor (drives eps_mca lower bound):
        ls = listSize(t)
        # the reverse dictionary forces interleaved list > L for the largest L with
        # 1 + (n - a_coll)*L < ls   (using eps_mca >= ls/q at the explosion band).
        # solve for L:
        if n - a_coll == 0:
            Lmax = None
        else:
            Lmax = (ls - 1 - 1) // (n - a_coll)  # largest L with 1+(n-a)*L <= ls-1 < ls
        a_J_local = a_J
        beyond = (a_coll <= a_J_local)
        print(f"     t={t} delta={Fraction(n-t,n)} a_coll={a_coll} listSize(t)={ls} "
              f"a_coll<=a_J={beyond}  forces interleaved list > L for L up to {Lmax}")
print()
print("  Interpretation: at a_coll <= a_J the Johnson interleaved cap is N/A, so ANY forced")
print("  list lower bound there is *beyond* what the Johnson machinery can deliver.  But the")
print("  forced L is O(1) (<= a few) at this tiny instance --- the magnitude is small; the VALUE")
print("  is the EXISTENCE of an unconditional interleaved list lower bound below the Johnson radius.")

print()
print("=== DONE ===")
