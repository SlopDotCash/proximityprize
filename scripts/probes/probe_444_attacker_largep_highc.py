#!/usr/bin/env python3
"""
probe_444_attacker_largep_highc.py  (#444 ATTACKER — the sharpest refutation attempt)

To REFUTE we need a defect with eta = c/n > eta_crit = log(s)/(2 log p), i.e. p > s^{n/(2c)}.
Best chance: LARGE c (many vanishing power sums) at LARGE p (so eta_crit shrinks).
For fixed s, eta_crit = log s/(2 log p) -> 0 as p -> infinity, while eta=c/n is FIXED by the
combinatorics. So if a defect with c>=2 SURVIVES to arbitrarily large p for fixed s, then for p
large enough eta_crit < eta and the floor is REFUTED.

THE CRUX QUESTION: for a fixed (n, s, c>=2), does a NON-char-0 defect persist as p grows, or does
it DISAPPEAR above the norm ceiling p = s^{n/(2c)}? The floor predicts it disappears: defects with
given (s,c) exist ONLY for p <= s^{n/(2c)} (= |C|^{1/(2eta)} ceiling). We test this directly:

For each (n, s, c) with c>=2, sweep p from small to LARGE and record the LARGEST prime p at which
a non-char-0 defect with EXACTLY-depth>=c still exists. Compare to the ceiling s^{n/(2c)}.
If the largest defect-prime EXCEEDS the ceiling, the norm bound is violated => REFUTED.
"""
import itertools, math, cmath
from math import comb, log
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e = []; x = 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def char0_survivor(n, idxs, c):
    z = 2j*math.pi/n
    pts = [cmath.exp(z*i) for i in idxs]
    for j in range(1, c+1):
        if abs(sum(pt**j for pt in pts)) > 1e-7:
            return False
    return True

def has_defect_depth_ge(n, p, s, c):
    """True if a NON-char-0 size-s set has p_1..p_c == 0 mod p (depth >= c)."""
    elts = subgroup(n, p)
    powtab = [[pow(v, j, p) for j in range(1, c+1)] for v in elts]
    for combo in itertools.combinations(range(n), s):
        ok = True
        for j in range(c):
            t = 0
            for i in combo:
                t += powtab[i][j]
            if t % p != 0:
                ok = False; break
        if ok and not char0_survivor(n, combo, c):
            return combo
    return None

def primes_1modn_upto(n, idx_min, pmax, pmin=0):
    out = []; pp = max(n+1, pmin)
    while pp <= pmax:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= idx_min:
            out.append(pp)
        pp += n
    return out

if __name__ == "__main__":
    print("### LARGE-p / HIGH-c refutation: does a (s,c>=2) defect survive ABOVE p=s^{n/(2c)}? ###\n")
    # n=16 and n=32. For each (s,c), find the LARGEST defect-prime and compare to ceiling.
    configs = [
        (16, 4, 2), (16, 5, 2), (16, 6, 2), (16, 8, 2), (16, 6, 3), (16, 8, 3), (16, 8, 4),
        (32, 4, 2), (32, 5, 2), (32, 6, 2), (32, 6, 3), (32, 8, 2), (32, 8, 3), (32, 8, 4),
    ]
    any_refute = False
    for (n, s, c) in configs:
        if comb(n, s) > 3_000_000:
            print(f"  n={n} s={s} c={c}: comb too big, skip"); continue
        eta = c / n
        ceil = s ** (n/(2*c))   # = s^{1/(2 eta)}
        # sweep primes up to a few times the ceiling (capped for runtime)
        pmax = int(min(ceil * 30, 4_000_000))
        primes = primes_1modn_upto(n, 2, pmax)
        largest_defect_p = None; ex = None
        eta_crit_at_largest = None
        n_above_ceiling_with_defect = 0
        for p in primes:
            d = has_defect_depth_ge(n, p, s, c)
            if d is not None:
                largest_defect_p = p; ex = d
                if p > ceil:
                    n_above_ceiling_with_defect += 1
        if largest_defect_p is None:
            print(f"  n={n} s={s} c={c} eta={eta:.4f}: NO (s,c)-defect at any p<= {pmax} "
                  f"(ceiling s^(n/2c)={ceil:.4g})")
            continue
        eta_crit_at_largest = log(s)/(2*log(largest_defect_p))
        refute = eta > eta_crit_at_largest
        tag = "  <<< REFUTES (defect above eta_crit)" if refute else ""
        if refute:
            any_refute = True
        print(f"  n={n} s={s} c={c} eta={eta:.4f}: ceiling p<=s^(n/2c)={ceil:.4g}; "
              f"LARGEST defect-prime={largest_defect_p} (>ceil? {largest_defect_p>ceil}); "
              f"#primes>ceil WITH defect={n_above_ceiling_with_defect}; "
              f"eta_crit@largest={eta_crit_at_largest:.4f} eta>ec?{refute}{tag}")
        if largest_defect_p > ceil:
            print(f"        NOTE: a defect EXISTS above the norm ceiling. ex T={list(ex)} at p={largest_defect_p}")
    print()
    print("REFUTED" if any_refute else "NO REFUTATION: every (s,c>=2) defect stays below its eta_crit / norm ceiling.")
