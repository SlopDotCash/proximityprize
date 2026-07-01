#!/usr/bin/env python3
"""
probe_cr_monotonicity_regime.py  (issue #444, [cr-monotonicity], regime-controlled)

The first probe (probe_cr_monotonicity.py) compared K_eff(n) across DIFFERENT primes
p with DIFFERENT beta = log_n(p). That is a confound: A_r = E_r - n^{2r}/p and E_r
itself both depend on p (extra mod-p sum coincidences appear when p is small relative
to the r-fold sumset width n^r). To get a clean K_eff extrapolation we must control p.

This probe does two controls:

 (1) FIXED-n, VARYING-p sweep: for each n, compute a_r over several primes p with
     n | p-1, to see whether a_r (hence K_eff) is p-stable or p-driven. The prize is at
     p ~ n*2^128 i.e. beta ~ 128 (HUGE p), so the relevant limit is p -> infinity, where
     n^{2r}/p -> 0 and E_r -> its char-0 / "clean" value (no mod-p coincidences below
     the wall). We approximate that limit with the LARGEST tractable p.

 (2) CHAR-0 LIMIT a_r: as p -> infinity at fixed n,r (and below the deep-moment wall),
     E_r -> E_r^{char0} = #{integer solutions sum a = sum b, a,b in mu_n lifted to roots
     of unity} ... but mu_n here is a multiplicative subgroup of F_p, not literal roots
     of unity. The clean-regime claim (KB) is E_r^{char-p} = E_r^{char-0} for r below the
     wall when n=2^mu. We test p-stability directly: if a_r is the same for the two
     largest primes, that IS the char-0 value to that precision.

DECISION: report a_r and K_eff at the LARGEST p per n (closest to prize beta), and the
spread across primes. Verdict = does K_eff(n) at the clean (large-p) value saturate < 1
or grow toward 1 as n: 16 -> 32 -> 64 -> 128?
"""

import itertools
from fractions import Fraction

def is_prime(p):
    if p < 2: return False
    if p % 2 == 0: return p == 2
    i = 3
    while i*i <= p:
        if p % i == 0: return False
        i += 2
    return True

def primes_with_subgroup(n, count, start=None):
    """First `count` primes p (proper: p-1 a strict multiple of n) with n | p-1."""
    out = []
    k = 2 if start is None else max(2, (start)//n)
    while len(out) < count:
        p = k*n + 1
        if is_prime(p) and (p-1) % n == 0 and (p-1) != n:
            out.append(p)
        k += 1
    return out

def subgroup_mu_n(p, n):
    def order(a):
        o, x = 1, a % p
        while x != 1:
            x = (x*a) % p; o += 1
        return o
    g = next(c for c in range(2, p) if order(c) == p-1)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    assert len(S) == n
    return sorted(S)

def energy_exact(S, p, r):
    cur = [0]*p
    for a in S: cur[a % p] += 1
    for _ in range(r-1):
        nxt = [0]*p
        for v in range(p):
            cv = cur[v]
            if cv:
                for a in S:
                    nxt[(v+a) % p] += cv
        cur = nxt
    return sum(c*c for c in cur)

def dfodd(r):
    res = 1
    for k in range(1, r+1): res *= (2*k-1)
    return res

def a_r_table(S, p, n, Rmax):
    rows = []
    for r in range(1, Rmax+1):
        E = energy_exact(S, p, r)
        Ar = Fraction(E) - Fraction(n**(2*r), p)
        Wick = dfodd(r)*(n**r)
        ar = Fraction(Ar, Wick)
        Keff = float(ar)**(1.0/r) if ar > 0 else float('nan')
        rows.append((r, E, float(ar), Keff))
    return rows

def main():
    print("ISSUE #444 [cr-monotonicity] regime-controlled: a_r / K_eff p-stability\n")
    # tractability: keep p modest; brute force is O(R*p*n).
    config = {16: (8, 6), 32: (6, 4), 64: (5, 3), 128: (4, 3)}
    summary = {}
    for n, (Rmax, nprimes) in config.items():
        ps = primes_with_subgroup(n, nprimes)
        print(f"==== n={n}: primes {ps} (beta=log_n p in "
              f"[{min(_logn(pp,n) for pp in ps):.2f},{max(_logn(pp,n) for pp in ps):.2f}]) ====")
        tabs = {p: a_r_table(subgroup_mu_n(p, n), p, n, Rmax) for p in ps}
        # print a_r per prime
        print(f"   r |  " + "  ".join(f"a_r@p={p:<6}" for p in ps) + "   | K_eff@maxp")
        biggest = ps[-1]
        for ri in range(Rmax):
            r = ri+1
            vals = [tabs[p][ri][2] for p in ps]
            Keff_big = tabs[biggest][ri][3]
            print(f"   {r:>1} |  " + "  ".join(f"{v:<9.5f}" for v in vals) +
                  f"   | {Keff_big:.5f}")
        summary[n] = tabs[biggest]
        print()

    print("==== CLEAN (largest-p) K_eff(n) EXTRAPOLATION ====")
    maxr = min(len(v) for v in summary.values())
    print(f"  r | " + " ".join(f"n={n:<6}" for n in summary))
    for ri in range(maxr):
        r = ri+1
        print(f"  {r:>1} | " + " ".join(f"{summary[n][ri][3]:<8.4f}" for n in summary))

    print("\n  VERDICT NOTE: a_r should be ~p-stable (clean regime) at these depths;")
    print("  if K_eff at fixed r is flat or DECREASING in n -> saturates (<1) -> prize plausible;")
    print("  if K_eff at fixed r INCREASES in n toward 1 -> floor in danger.")

def _logn(p, n):
    from math import log
    return log(p)/log(n)

if __name__ == "__main__":
    main()
