#!/usr/bin/env python3
"""[sweep][A08]  WORST window-interior monomial direction over ALL (a,b) with b-a>1, at fixed
window-interior agreement size w (= fixed delta), for n=8,16 in F_q and char-0.

This complements sweep_A08_window_interior.py (which fixes b-a=2, a=w-1).  Here a fixed DIRECTION
dir(a,b) is a pair of monomial degrees, and we vary it freely (b-a in {2,3,...}) to locate the
direction that MAXIMIZES #bad at a window-interior delta.  Decide O(n) vs super-linear at the worst.

bad(a,b,w) = #{ gamma!=0 : exists |S|=w subset of mu_n with (X^b+gamma X^a) mod m_S of degree < k },
k = rho*n.  Window-interior: johnson < delta=1-w/n < capacity, and we keep w-k>=2 rows.
"""
import sys, os
from itertools import combinations
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyclotomic_exact_enumerator import gen_mu, monomial_mod_Fq

_MU = {}
def mu(q, n):
    if (q, n) not in _MU:
        _MU[(q, n)] = gen_mu(q, n)
    return _MU[(q, n)]

def bad_dir_Fq(n, k, a, b, q, w):
    g = mu(q, n)
    bad = set()
    inv = lambda x: pow(x, q - 2, q)
    # precompute X^a, X^b residues per subset on the fly
    for Sidx in combinations(range(n), w):
        vals = [g[i] for i in Sidx]
        Pa = monomial_mod_Fq(vals, a, q); Pb = monomial_mod_Fq(vals, b, q)
        gamma = None; ok = True
        for j in range(k, w):
            ca, cb = Pa[j] % q, Pb[j] % q
            if ca == 0:
                if cb != 0: ok = False; break
            else:
                cand = (-cb * inv(ca)) % q
                if gamma is None: gamma = cand
                elif gamma != cand: ok = False; break
        if ok and gamma is not None and gamma != 0:
            bad.add(gamma)
    return len(bad)

if __name__ == "__main__":
    print("=" * 92)
    print("[A08] WORST direction over (a,b), b-a>1, at fixed window-interior delta.  n=8,16.")
    print("=" * 92)
    PRIMES = {8: [97, 337, 769], 16: [193, 353, 769]}
    for n in (8, 16):
        for rho in (0.5, 0.25):
            k = int(round(rho * n))
            johnson = 1 - rho ** 0.5; capacity = 1 - rho
            for w in range(k + 2, n):
                delta = 1 - w / n
                if not (johnson < delta < capacity):
                    continue
                if comb(n, w) > 400000:
                    continue
                print(f"\n--- n={n} rho={rho} k={k} w={w} delta={delta:.3f} "
                      f"(window {johnson:.3f}..{capacity:.3f}), rows={w-k} ---")
                # sweep directions: a in (k, ..), b=a+gap, gap in 2..(some bound), b<=2n-1.
                best = (0, None)
                for a in range(k, 2 * n):
                    for gap in range(2, 6):
                        b = a + gap
                        if b > 2 * n - 1:
                            continue
                        cnts = [bad_dir_Fq(n, k, a, b, q, w) for q in PRIMES[n]]
                        mx = max(cnts)
                        if mx > best[0]:
                            best = (mx, (a, b, cnts))
                        # only print non-trivial directions
                        if mx >= 1:
                            flag = "<=n" if mx <= n else "~%.2fn" % (mx / n)
                            print(f"    dir({a},{b}) gap={gap}: F_q #bad={cnts}  [worst {flag}]")
                if best[1]:
                    a, b, cnts = best[1]
                    flag = "<=n" if best[0] <= n else "~%.2fn" % (best[0] / n)
                    print(f"    >>> WORST: dir({a},{b}) #bad={best[0]} [{flag}]")
                else:
                    print("    (no bad scalars in any direction at this delta)")
