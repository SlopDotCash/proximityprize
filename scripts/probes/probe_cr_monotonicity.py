#!/usr/bin/env python3
"""
probe_cr_monotonicity.py  (issue #444, [cr-monotonicity])

Goal
----
The prize reduces (proven spines) to A_r = E_r - n^{2r}/q <= Wick_r := (2r-1)!!*n^r
at depth r ~ log m ~ 128, where E_r = additive energy of order r of mu_n =
zeroSumCount(mu_n, 2r) = #{(a_1..a_r, b_1..b_r) in mu_n^{2r} : sum a = sum b}.

The normalized recursion (orchestrator line 5733) is
    a_{r+1} = (a_r + 2r * c_r) / (1 + 2r),    a_r := A_r / Wick_r,
so that, given the measured a_r trajectory,
    c_r = ((1 + 2r) * a_{r+1} - a_r) / (2r).
The prize collapses to c_r <= 1 for all r up to log m. Equivalently a_r <= 1 for all r
(A_r <= Wick_r) is the Wick bound itself; the recursion shows a_{r+1} is a convex
combination of a_r and c_r, so a_r<=1 holds for all r iff sup_r c_r <= 1 AND a_1<=1.

This probe computes, EXACTLY (brute force over a PROPER subgroup mu_n of F_p*, never
the full group):
  - E_r = zeroSumCount(mu_n, 2r) for r = 1..R
  - A_r = E_r - n^{2r}/p     (DC-subtracted, the prize object)
  - Wick_r = (2r-1)!! * n^r
  - a_r = A_r / Wick_r
  - c_r from the recursion
  - K_eff(n) = a_r^{1/r}   (the decisive extrapolation across n)

DECISION OUTPUTS:
  (a) does c_r <= 1 hold at shallow r (r <= 8)?
  (b) does K_eff(n) SATURATE (-> prize plausibly true) or GROW past 1 (-> floor in danger)?
"""

import itertools
from fractions import Fraction
from math import gcd

# ---------------------------------------------------------------------------
# field / subgroup helpers
# ---------------------------------------------------------------------------

def is_prime(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    i = 3
    while i * i <= p:
        if p % i == 0:
            return False
        i += 2
    return True

def find_prime_with_subgroup(n, start):
    """Smallest prime p >= start with n | p-1 (so mu_n exists, PROPER since p-1 > n)."""
    # we want a PROPER subgroup: p-1 must be a STRICT multiple of n
    k = (start - 1) // n
    if k < 2:
        k = 2          # force p-1 >= 2n  => proper, never the full group
    while True:
        p = k * n + 1
        if p > start and is_prime(p) and (p - 1) % n == 0 and (p - 1) != n:
            return p
        k += 1

def subgroup_mu_n(p, n):
    """Return the order-n multiplicative subgroup mu_n of F_p* as a sorted list."""
    assert (p - 1) % n == 0
    # find a generator g of F_p*, then g^{(p-1)/n} generates mu_n
    def order(a):
        o, x = 1, a % p
        while x != 1:
            x = (x * a) % p
            o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p - 1:
            g = cand
            break
    assert g is not None
    h = pow(g, (p - 1) // n, p)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x * h) % p
    assert len(S) == n, (len(S), n)
    return sorted(S)

# ---------------------------------------------------------------------------
# exact energy E_r = zeroSumCount(mu_n, 2r) over F_p
# ---------------------------------------------------------------------------

def energy_exact(S, p, r):
    """
    E_r = #{(a_1..a_r,b_1..b_r) in S^{2r} : sum a = sum b mod p}.
    Computed by convolution of the r-fold sumset multiplicity vector.
    cnt[r][v] = # of r-tuples from S summing to v mod p.  Then
    E_r = sum_v cnt[r][v]^2.
    """
    n = len(S)
    # cnt for 1 element
    cnt = [0] * p
    for a in S:
        cnt[a % p] += 1
    powcnt = [cnt[:]]  # powcnt[k] = distribution of (k+1)-fold sums
    cur = cnt[:]
    for _ in range(r - 1):
        nxt = [0] * p
        for v in range(p):
            cv = cur[v]
            if cv == 0:
                continue
            for a in S:
                nxt[(v + a) % p] += cv  # multiply multiplicities
        cur = nxt
        powcnt.append(cur)
    dist = powcnt[r - 1]
    E = sum(c * c for c in dist)
    return E

# ---------------------------------------------------------------------------
# Wick / DC objects
# ---------------------------------------------------------------------------

def double_factorial_odd(r):
    """(2r-1)!! = product of odd numbers 1*3*5*...*(2r-1)."""
    res = 1
    for k in range(1, r + 1):
        res *= (2 * k - 1)
    return res

def analyze(n, start_prime):
    p = find_prime_with_subgroup(n, start_prime)
    S = subgroup_mu_n(p, n)
    proper = (p - 1) != n
    print(f"\n==== mu_n: n={n}, p={p}  (p-1={p-1}={ (p-1)//n }*n, proper={proper}) ====")

    # how deep can we afford? energy_exact is O(R * p * n) in time, O(p) memory.
    Rmax = 8 if n <= 16 else (6 if n <= 32 else (5 if n <= 64 else 4))
    rows = []
    for r in range(1, Rmax + 1):
        E = energy_exact(S, p, r)
        # A_r = E_r - n^{2r}/p  (DC subtraction; exact rational)
        Ar = Fraction(E) - Fraction(n ** (2 * r), p)
        Wick = double_factorial_odd(r) * (n ** r)
        ar = Fraction(Ar, Wick)
        Keff = float(ar) ** (1.0 / r) if ar > 0 else float('nan')
        rows.append((r, E, Ar, Wick, ar, Keff))

    # print table
    print(f"{'r':>2} {'E_r':>16} {'A_r(float)':>16} {'Wick_r':>16} {'a_r':>10} {'K_eff':>8} {'c_r':>10}")
    for i, (r, E, Ar, Wick, ar, Keff) in enumerate(rows):
        # c_r from recursion using a_{r+1}
        if i + 1 < len(rows):
            ar1 = rows[i + 1][4]
            cr = ((1 + 2 * r) * ar1 - ar) / (2 * r)
            cr_str = f"{float(cr):.5f}"
            cr_le1 = float(cr) <= 1.0 + 1e-12
        else:
            cr_str = "   --   "
            cr_le1 = None
        flag = "" if (cr_le1 is None) else (" OK" if cr_le1 else " >1 !!")
        print(f"{r:>2} {E:>16} {float(Ar):>16.4f} {Wick:>16} "
              f"{float(ar):>10.5f} {Keff:>8.5f} {cr_str:>10}{flag}")
    return n, p, rows

def main():
    print("ISSUE #444 [cr-monotonicity]: c_r and K_eff trajectory over PROPER mu_n")
    print("E_r = zeroSumCount(mu_n,2r); A_r = E_r - n^{2r}/p; Wick_r=(2r-1)!!*n^r;")
    print("a_r = A_r/Wick_r; c_r from a_{r+1}=(a_r+2r c_r)/(1+2r); K_eff=a_r^{1/r}.")

    results = []
    # use moderate primes so brute force is tractable; PROPER subgroups
    for n, start in [(16, 100), (32, 200), (64, 400), (128, 800)]:
        results.append(analyze(n, start))

    # K_eff extrapolation summary at small r (r=2,3,4 where all n reach)
    print("\n\n==== K_eff(n) EXTRAPOLATION (does it saturate or grow past 1?) ====")
    print(f"{'r':>3} | " + " ".join(f"n={n:<5}" for n, _, _ in results))
    maxr = min(len(rows) for _, _, rows in results)
    for r in range(1, maxr + 1):
        vals = []
        for _, _, rows in results:
            _, _, _, _, _, Keff = rows[r - 1]
            vals.append(Keff)
        print(f"{r:>3} | " + " ".join(f"{v:<7.4f}" for v in vals))

    # c_r shallow verdict
    print("\n==== c_r <= 1 SHALLOW VERDICT (r <= 8) ====")
    any_violation = False
    for n, p, rows in results:
        for i in range(len(rows) - 1):
            r = rows[i][0]
            ar = rows[i][4]
            ar1 = rows[i + 1][4]
            cr = ((1 + 2 * r) * ar1 - ar) / (2 * r)
            if float(cr) > 1.0 + 1e-9:
                any_violation = True
                print(f"  VIOLATION n={n} r={r}: c_r={float(cr):.5f} > 1")
    if not any_violation:
        print("  c_r <= 1 holds at ALL measured shallow rungs (r<=8) for all n.")

if __name__ == "__main__":
    main()
