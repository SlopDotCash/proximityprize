#!/usr/bin/env python3
"""[sweep][A08]  Growth law of the b-a=2 rows=2 (near-capacity edge) #bad, and the rows>=3
interior collapse.   Cheap cells only: small w, where C(n,w) is enumerable up to n=64.

For dir(w-1,w+1) at k=w-2 (rows=2): #bad = #{ gamma : exists |S|=w with e_3(S)=e_1(S) e_2(S),
gamma = e_2 - e_1^2 != 0 }.  We tabulate this over n=8..64 at the SMALLEST window-interior w that
is feasible, to fit #bad ~ Theta(n^c).  Also re-confirm the rows=3 collapse (one more vanishing
symmetric-function row).
"""
import sys, os
from itertools import combinations
from math import comb, log
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyclotomic_exact_enumerator import gen_mu, esym_Fq

_MU = {}
def mu(q, n):
    if (q, n) not in _MU:
        _MU[(q, n)] = gen_mu(q, n)
    return _MU[(q, n)]

def bad_rows2(n, w, q):
    """rows=2 cell, dir(w-1,w+1), k=w-2: gamma=e_2-e_1^2, constraint e_3=e_1 e_2."""
    g = mu(q, n)
    if g is None: return None
    bad = set()
    for Sidx in combinations(range(n), w):
        vals = [g[i] for i in Sidx]
        e = esym_Fq(vals, q)
        e1, e2, e3 = e[1] % q, e[2] % q, e[3] % q
        if (e3 - e1 * e2) % q == 0:
            gamma = (e2 - e1 * e1) % q
            if gamma != 0:
                bad.add(gamma)
    return len(bad)

def bad_rows3(n, w, q):
    """rows=3 cell: dir(w-1, w+2) at k=w-3 (three top coeffs vanish).  Direct via residues would
    need the enumerator; here we use the symmetric-function form is messier, so just report the
    count from the general monomial reducer."""
    from cyclotomic_exact_enumerator import monomial_mod_Fq
    g = mu(q, n); a, b, k = w - 1, w + 2, w - 3
    bad = set()
    for Sidx in combinations(range(n), w):
        vals = [g[i] for i in Sidx]
        Pa = monomial_mod_Fq(vals, a, q); Pb = monomial_mod_Fq(vals, b, q)
        gamma = None; ok = True
        for j in range(k, w):
            ca, cb = Pa[j] % q, Pb[j] % q
            if ca == 0:
                if cb != 0: ok = False; break
            else:
                cand = (-cb * pow(ca, q - 2, q)) % q
                if gamma is None: gamma = cand
                elif gamma != cand: ok = False; break
        if ok and gamma is not None and gamma != 0:
            bad.add(gamma)
    return len(bad)

if __name__ == "__main__":
    print("=" * 80)
    print("[A08] Growth law: rows=2 (b-a=2, near-capacity edge) #bad vs n.")
    print("  dir(w-1,w+1), k=w-2; gamma=e_2-e_1^2, constraint e_3=e_1 e_2.")
    print("=" * 80)
    # use w=4 (k=2, rho=2/n) across n; C(n,4) feasible to n=64 (~635k).  Big-prime ~ char-0.
    PR = {8: 769, 16: 769, 32: 769, 64: 769}
    print("\n  w=4 cell (k=2): #bad over n, large prime q=769:")
    pts = []
    for n in (8, 16, 32, 64):
        q = PR[n]
        if comb(n, 4) > 1500000:
            print(f"    n={n}: SKIP"); continue
        nb = bad_rows2(n, 4, q)
        pts.append((n, nb))
        print(f"    n={n:3d}: #bad={nb:5d}   #bad/n={nb/n:6.2f}   #bad/n^1.5={nb/n**1.5:5.2f}   #bad/n^2={nb/n**2:5.3f}")
    if len(pts) >= 2:
        import math
        for i in range(1, len(pts)):
            (n0, b0), (n1, b1) = pts[i - 1], pts[i]
            if b0 and b1:
                c = math.log(b1 / b0) / math.log(n1 / n0)
                print(f"    fitted exponent c on [{n0},{n1}]:  #bad ~ n^{c:.3f}")
    # q-dependence at fixed n=32, w=4:
    print("\n  q-dependence of the rows=2 #bad (n=32, w=4) across primes q=1 mod 32:")
    for q in (97, 193, 257, 449, 577, 769, 929):
        if mu(q, 32) is None: continue
        print(f"    q={q:4d}: #bad={bad_rows2(32, 4, q)}")
    print("\n  rows=3 interior collapse (dir(w-1,w+2), k=w-3), n=16:")
    for w in (5, 6, 7):
        for q in (97, 193, 769):
            print(f"    n=16 w={w} dir({w-1},{w+2}) k={w-3}: q={q} #bad={bad_rows3(16, w, q)}")
