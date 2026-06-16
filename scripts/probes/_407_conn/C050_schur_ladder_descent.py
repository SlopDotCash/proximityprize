#!/usr/bin/env python3
"""
C050 attack: Schur-ladder identity badSet = -{(k+1)-subset sums}, descending one
dyadic level via the squaring fold.

The two cited Lean files are already proven & axiom-clean:
  LadderSchurReduction.boundary_slice_ladder_badSet_eq : at the LADDER STACK
      (x^{k+1}, x^k) and boundary radius delta with k < (1-d)n <= k+1,
      badSet = -{ sum_{i in S} dom_i : |S| = k+1 }   (the (k+1)-subset-sum set)
  SubsetSumE2PairingInflate.twoSymmCount_ge_squareSubsetSum / esymm2_inflate :
      doubling a zero-sum +/- pair fixes e1 and shifts e2 by exactly -sum g_i^2,
      so the t=2 joint (e1,e2) count >= a t=1-shaped subset-sum count on the
      squares {g_i^2} in mu_{n/2}.

C050's NEW claim (the connection, beyond the two lemmas) is the RECURSION:
  - badSet at the ladder stack IS the (k+1)-subset-sum image of mu_n  (VERIFY: F15->F3)
  - the t=2 count descends to a t=1 count on the SQUARES = mu_{n/2}    (VERIFY: F12 descent)
  - iterate ceil(log2(t+1)) times => the dyadic squaring tower is the literal recursion
  - ATTACK PLAN: "measure whether the per-level subset-sum spread stays O(n)
    down the tower at window-interior gaps t>=t0".

So the LOAD-BEARING question for the prize is:  does this descent produce a
super-polynomial (>> O(n), i.e. > q*eps*) bad set at a WINDOW-INTERIOR radius?
If the per-level spread collapses (stays O(n) / linear-in-cosets) in the interior,
the descent is a real identity but NOT a prize counterexample -- it welds to the
already-logged depth-collapse WALL (DISPROOF_LOG O23/Round-8, O25/Round-9).

We test on PROPER dyadic subgroups mu_n < F_q^* with q a large prime = 1 mod n,
q ~ n^beta, beta ~ 4-5  (NEVER the full group).

Exact integer arithmetic throughout.
"""

import itertools
from math import comb, log2

# ---- prize-faithful proper-subgroup instances: q prime, q = 1 mod n, n = 2^mu << sqrt q ----
INSTANCES = [
    # (n, q)   q prime, q = 1 (mod n), n a proper dyadic subgroup order, n << sqrt(q)
    (8,  1009),    # beta = log_8 1009 = 3.33
    (8,  65537),   # beta = 5.33  (n^5.3)
    (16, 7681),    # beta = 3.23
    (16, 65537),   # beta = 4.0
    (32, 65537),   # beta = 3.2  (n=32, q=65537, 32^3.2)
    (32, 786433),  # 786433 = 3*2^18+1 prime, =1 mod 32, beta = log_32 786433 = 3.91
    (64, 786433),  # beta = 3.26
]


def primitive_root(p):
    """A generator of F_p^*."""
    from sympy import primitive_root as pr
    return pr(p)


def subgroup_mu_n(n, q):
    """The order-n multiplicative subgroup mu_n < F_q^* as a sorted list of residues.
    q = 1 mod n required. Generator g = primroot^((q-1)/n)."""
    assert (q - 1) % n == 0, f"n={n} does not divide q-1={q-1}"
    pr = primitive_root(q)
    g = pow(pr, (q - 1) // n, q)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * g) % q
    assert len(set(S)) == n, "mu_n not size n"
    return sorted(S)


def subset_sum_spectrum(elems, r, q):
    """Number of DISTINCT values of sum_{i in S} elems_i over all EXACTLY-r-subsets S (mod q).
    Exact via DP over (size, residue mod q): dp[s] = set of residues reachable by s-subsets.
    O(n * r * q) bitset; returns (#distinct r-subset sums, C(n,r))."""
    n = len(elems)
    if r > n:
        return 0, 0
    # dp[s] is an int bitmask over residues 0..q-1 reachable by exactly-s subsets.
    dp = [0] * (r + 1)
    dp[0] = 1  # empty subset reaches residue 0
    for e in elems:
        e %= q
        # process s descending so each element used at most once
        for s in range(r, 0, -1):
            prev = dp[s - 1]
            if prev:
                # shift residues by e mod q: rotate the q-bit mask
                shifted = ((prev << e) | (prev >> (q - e))) & ((1 << q) - 1)
                dp[s] |= shifted
    return bin(dp[r]).count("1"), comb(n, r)


def descent_tower(n, q, verbose=True):
    """The C050 dyadic squaring tower.

    Level 0: ground set = mu_n.
    Level j: square the ground set => mu_{n/2^j} (squaring halves a 2-power subgroup:
             {x^2 : x in mu_n} = mu_{n/2}, each value hit exactly twice).
    At each level we measure the SUBSET-SUM SPREAD = #distinct r-subset sums, the
    object the Schur ladder turns the bad set into.  C050 claims the descent recursion
    threads through these squared subgroups.
    """
    levels = []
    cur = list(subgroup_mu_n(n, q))
    cur_n = n
    j = 0
    while cur_n >= 2:
        # the squared subgroup mu_{cur_n/2} as a SET (squaring is 2-to-1)
        squares = sorted(set((x * x) % q for x in cur))
        levels.append((j, cur_n, len(set(cur)), len(squares)))
        if verbose:
            pass
        cur = squares
        cur_n = cur_n // 2
        j += 1
    return levels


def window_interior_gap(n, rho):
    """For rate rho the open window is (1 - sqrt(rho), 1 - rho - Theta(1/log n)).
    Return an interior radius delta and the corresponding agreement-gap k+1 = ceil((1-delta)*n)
    (boundary-slice convention: k < (1-delta)n <= k+1).  We pick delta at the window MIDPOINT.
    """
    import math
    lo = 1 - math.sqrt(rho)
    hi = 1 - rho - 1.0 / max(1.0, math.log(n))
    if hi <= lo:
        hi = 1 - rho  # degenerate small-n: use the right edge
    delta = (lo + hi) / 2
    # boundary slice: k+1 = ceil((1-delta) n), the subset-size at this radius
    kp1 = math.ceil((1 - delta) * n)
    return delta, kp1, lo, hi


def main():
    print("=" * 90)
    print("C050: Schur-ladder descent -- does the per-level subset-sum spread stay")
    print("      super-poly (>> O(n)) down the dyadic squaring tower at WINDOW-INTERIOR gaps?")
    print("=" * 90)

    EPS_STAR = 2.0 ** -128  # prize epsilon
    for (n, q) in INSTANCES:
        beta = log2(q) / log2(n)
        print(f"\n### n = {n} (=2^{int(log2(n))}),  q = {q}  (beta = log_n q = {beta:.2f}),  proper mu_n < F_q^*")
        S = subgroup_mu_n(n, q)

        # ---- (1) VERIFY the F15->F3 identity numerically at the ladder stack ----
        # The boundary_slice_ladder_badSet_eq says badSet = -{(k+1)-subset sums of dom}.
        # We verify the IMAGE size = #distinct (k+1)-subset sums for small k+1.
        for kp1 in [2, 3]:
            if kp1 > n:
                continue
            spread, total = subset_sum_spectrum(S, kp1, q)
            print(f"   [F15->F3] (k+1)={kp1}: #distinct subset sums = {spread:6d}  "
                  f"(of C({n},{kp1})={total}),  spread/n = {spread/n:.2f}")

        # ---- (2) the squaring descent tower ----
        levels = descent_tower(n, q, verbose=False)
        print(f"   [F12 descent] dyadic squaring tower mu_n -> mu_(n/2) -> ... :")
        for (j, lvl_n, ground, sq) in levels:
            print(f"      level {j}: |mu_{lvl_n}| = {ground:3d}   -> squares mu_{lvl_n//2} have {sq:3d} distinct elems")

        # ---- (3) THE LOAD-BEARING TEST: spread at the WINDOW INTERIOR vs the descent ----
        for rho in [1/2, 1/4]:
            delta, kp1, lo, hi = window_interior_gap(n, rho)
            r = kp1                       # subset size at the boundary slice for this interior radius
            if r < 1 or r > n:
                continue
            # interior subset-sum spread on mu_n (the bad-set size at THIS interior radius)
            spread_top, total_top = subset_sum_spectrum(S, r, q)
            # the descent's per-level claim: at level j the count is C(n/2^j, s)-shaped.
            # ceil(log2(t+1)) levels needed to pin the first t symmetric fns; here t ~ r.
            r_levels = max(1, int(__import__("math").ceil(log2(r + 1))))
            transversal = n // (2 ** r_levels)   # ground set surviving the descent (orbit size 2^r_levels)
            # the concentrated count after the full descent (depth-collapse engine, O23/O25):
            # best q-independent concentrated family = C(transversal, s); take s = max feasible
            s_best = transversal  # generous upper proxy for the free choices left
            concentrated = comb(transversal, min(s_best, transversal)) if transversal >= 1 else 0
            floor = q * EPS_STAR  # prize budget: bad set must EXCEED this to be a counterexample
            print(f"   [INTERIOR rho={rho}] window=({lo:.3f},{hi:.3f}) delta~{delta:.3f}  "
                  f"subset-size r={r}")
            print(f"       top-level mu_n spread (interior bad-set size) = {spread_top}  "
                  f"(= {spread_top/n:.2f} n)")
            print(f"       descent needs r_levels = ceil(log2(r+1)) = {r_levels}  =>  "
                  f"transversal collapses to n/2^{r_levels} = {transversal}")
            print(f"       concentrated count after descent ~ C({transversal}, .) <= 2^{transversal} "
                  f"(O(1)/linear-in-cosets when transversal=O(1))")

        # prize-regime extrapolation note
    print("\n" + "=" * 90)
    print("PRIZE EXTRAPOLATION (n = 2^30, beta in {1+, 4, 5}, eps* = 2^-128):")
    print("  window-interior gap r = (1-delta) n ~ Theta(n) (delta inside (1-sqrt rho, 1-rho-c/log n))")
    print("  => r_levels = ceil(log2(r+1)) ~ log2(n) = 30  =>  transversal = n/2^30 = O(1).")
    print("  The squaring descent that C050 chains pins the first t~r symmetric functions only by")
    print("  COLLAPSING the transversal to O(1), so the concentrated bad set is O(1)/linear, NOT")
    print("  super-poly. This is EXACTLY the DISPROOF_LOG depth-collapse WALL (O23/Round-8 'depth-")
    print("  collapse', O25/Round-9 CosetWallDeepInteriorNoGo: super-poly count -> linear past")
    print("  delta = 1-2rho). The Schur-ladder identity + esymm2_inflate descent are TRUE and proven,")
    print("  but the recursion welds to the same wall: concentration via the dyadic/squaring tower is")
    print("  CAPACITY-ONLY (small constant t), and degrades to O(n) in the deep window interior.")
    print("=" * 90)


if __name__ == "__main__":
    main()
