#!/usr/bin/env python3
# wf407w2_L4-onq_min_norm.py
#
# Thread L4-onq (#407 prize). Second deliverable: the SMALLEST defect-carrying norm
#   min |N(e2(S))|  over window w-subsets S, alpha=e2(S)!=0 in char 0.
#
# WHY: the carrier-onset law (A09) is  S is a halo carrier mod q  <=>  q | N(e2(S)).
# So the SMALLEST nonzero |N(e2(S))| controls the SMALLEST prime q that can EVER be a
# defect carrier == the FIRST adversarial prime / the onset lever.  (The largest norm is
# the worst-case-q lever, already studied; the smallest is the ONSET lever, asked here.)
#
# We compute, per (n,w):
#   * min |N(alpha)| over alpha=e2(S)!=0  (= smallest carrier norm),
#   * the smallest prime q=1 mod n dividing SOME N(alpha)  (= first adversarial prime),
#   * how the smallest norm scales with n  (does the onset prime stay small or grow?).
#
# EXACT (resultant = cyclotomic field norm). Run: python <thisfile>

import itertools
from math import comb, log2, gcd
from sympy import symbols, Poly, resultant, cyclotomic_poly, totient, factorint, isprime

X = symbols('X')

def vec_e2(A, n):
    h = n//2
    v = [0]*h
    L = list(A)
    for a in range(len(L)):
        for b in range(a+1, len(L)):
            e = (L[a]+L[b]) % n
            if e < h: v[e] += 1
            else: v[e-h] -= 1
    return tuple(v)

def field_norm(v, Phi):
    a = Poly(sum(c*X**i for i, c in enumerate(v)), X)
    return int(resultant(Phi, a))

def analyze(n, w):
    Phi = Poly(cyclotomic_poly(n, X), X)
    seeds = set()
    for A in itertools.combinations(range(n), w):
        v = vec_e2(A, n)
        if any(v):
            seeds.add(v)
    norms = {}
    for v in seeds:
        N = field_norm(list(v), Phi)
        if N != 0:
            norms[v] = abs(N)
    if not norms:
        return None
    nz = sorted(set(norms.values()))
    mn, mx = nz[0], nz[-1]
    # smallest prime q = 1 mod n dividing some norm
    onset = None
    cand = set()
    for N in nz:
        for q in factorint(N):
            if q % n == 1 and q > 2:
                cand.add(q)
    if cand:
        onset = min(cand)
    return mn, mx, nz[:8], onset

if __name__ == "__main__":
    print("wf407-w2 / L4-onq : SMALLEST defect-carrying norm min|N(e2(S))| = ONSET lever")
    print("="*78)
    print(f"  {'n':>4} {'w':>3} {'phi':>5} {'min|N|':>10} {'log2min':>8} {'min/n':>7} "
          f"{'max|N|':>14} {'onset-q':>9}")
    for (n, w) in [(8,3),(8,4),(8,6),(16,4),(16,6),(16,8)]:
        r = analyze(n, w)
        if r is None:
            print(f"  {n:>4} {w:>3}   (no nonzero e2 seeds)", flush=True)
            continue
        mn, mx, low, onset = r
        ph = int(totient(n))
        print(f"  {n:>4} {w:>3} {ph:>5} {mn:>10} {log2(mn):>8.2f} {mn/n:>7.2f} "
              f"{mx:>14} {str(onset):>9}", flush=True)
        print(f"        smallest few |N|: {low}", flush=True)
    print("\n  ONSET interpretation: the smallest prime q=1 mod n dividing some N(e2(S)) is the")
    print("  FIRST q at which the e2=0 defect can turn on. Below it, defect=0 (clean) for ALL")
    print("  q=1 mod n. This is the lower edge of the carrier-prime band.")
