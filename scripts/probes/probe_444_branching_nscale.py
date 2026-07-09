#!/usr/bin/env python3
"""
probe_444_branching_nscale.py  (#444 SEAM A -- Refuter B, n-scaling crux)

Decisive n-scaling test of per-level descent branching at FIXED (k, eta), for both
descent regimes, WITHOUT the prohibitively slow exhaustive worst-word search.

We test, at each n, a small set of STRUCTURALLY-EXTREMAL weight-2 words and report the
max parent_L and its branching B_pair = parent_L / child_pairs:
  * MIXED-parity extremal: x^{n-1}+x^j (odd high exp + even low exp) -> monomial pair child.
  * SAME-parity extremal:  x^{n/4}+x^0 (both even) -> weight-2 child (halves).
Two primes per n. Window-interior eta in {0.0625,0.125,0.25}. mu_n proper, n!=p-1,
x^{n/2}=+-1 directions excluded. Exact arithmetic.

Branching is the quantity the constant-list bound needs O(1)/stable; if B_pair GROWS
with n at fixed (k,eta), the bound degrades (a REFUTATION).
"""
import itertools, sys, os
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_444_branching_factor import (find_window_prime, subgroup, list_RS,
    window_s, split_even_odd, descend_word, terms_to_word, word_structure)

def measure_word(n, a, b, k, eta, p):
    """parent_L and branching for the specific weight-2 word x^a+x^b at (n,k,eta)."""
    N = n // 2
    elts = subgroup(n, p); s = window_s(k, n, eta)
    u = [(pow(x, a, p) + pow(x, b, p)) % p for x in elts]
    members = list_RS(u, elts, k, s, p, return_members=True)
    parent_L = len(members)
    eltsN = subgroup(N, p)
    ue_t, uo_t = descend_word(a, b, n)
    ue_w = terms_to_word(ue_t, eltsN, p); uo_w = terms_to_word(uo_t, eltsN, p)
    kF = (k + 1) // 2; kG = k // 2
    childF = childG = None; sF = sG = None
    if 1 <= kF < N and comb(N, kF) <= 3_000_000:
        sF = window_s(kF, N, eta); childF = list_RS(ue_w, eltsN, kF, sF, p)
    if 1 <= kG < N and comb(N, kG) <= 3_000_000:
        sG = window_s(kG, N, eta); childG = list_RS(uo_w, eltsN, kG, sG, p)
    cp = (childF * childG) if (childF and childG) else None
    proj = len(set(split_even_odd(c, p) for c in members))
    return dict(a=a, b=b, parent_L=parent_L, s=s, childF=childF, childG=childG,
                child_pairs=cp, proj=proj,
                ue=word_structure(ue_t), uo=word_structure(uo_t),
                B_pair=(parent_L/cp if cp else None),
                B_F=(parent_L/childF if childF else None))

def candidates(n, k):
    """structurally-extremal weight-2 exponent pairs (avoid x^{n/2})."""
    h = n // 2
    cset = set()
    # mixed-parity (monomial-pair child): high odd + low even, and symmetric variants
    for j in range(0, min(k + 2, n)):
        for hi in (n - 1, n - 3):
            if hi != h and j != h and hi != j:
                cset.add((hi, j))
    # mixed: high even + low odd
    for j in (1, 3):
        for hi in (n - 2, n - 4):
            if hi != h and j != h and hi != j:
                cset.add((hi, j))
    # same-parity both-even (weight-2 child, halves): x^{n/4}+x^0 and neighbors
    for hi in (n // 4, n // 4 + 2, n // 2 - 2):
        if hi != h and hi != 0:
            cset.add((hi, 0))
    # same-parity both-odd
    for hi in (n // 4 + 1, n // 4 - 1):
        if 0 < hi < n and hi != h:
            cset.add((hi, 1))
    return [(max(a, b), min(a, b)) for (a, b) in cset if a != b]

def run():
    print("="*78)
    print("n-SCALING of per-level descent branching (structural extremal words)")
    print("="*78)
    from collections import defaultdict
    summary = defaultdict(list)
    for eta in (0.0625, 0.125, 0.25):
        for k in (2, 4):
            for n in (16, 32, 64):
                if comb(n, k) > 3_000_000:
                    continue
                primes = [find_window_prime(n, 4.0)]
                p2 = find_window_prime(n, 4.5)
                if p2 != primes[0]:
                    primes.append(p2)
                for p in primes:
                    best = None
                    for (a, b) in candidates(n, k):
                        try:
                            r = measure_word(n, a, b, k, eta, p)
                        except Exception:
                            continue
                        if best is None or r['parent_L'] > best['parent_L']:
                            best = r
                    if best is None:
                        continue
                    print(f"  n={n:3d} k={k} eta={eta:<6} p={p:>11d}: "
                          f"WORST x^{best['a']}+x^{best['b']} parent_L={best['parent_L']:>4} "
                          f"s={best['s']}  child=({best['childF']},{best['childG']}) "
                          f"pairs={best['child_pairs']}  proj={best['proj']}  "
                          f"B_pair={best['B_pair']}  B_F={best['B_F']}  "
                          f"[ue={best['ue']}|uo={best['uo']}]")
                    summary[(k, eta, n)].append((p, best['parent_L'], best['child_pairs'],
                                                 best['B_pair'], best['B_F']))
    print("\n" + "="*78)
    print("CRUX: B_pair across n at fixed (k,eta) -- does it GROW with n?")
    print("="*78)
    seen_ke = set((k, eta) for (k, eta, n) in summary)
    for (k, eta) in sorted(seen_ke):
        print(f"  (k={k}, eta={eta}):")
        for n in (16, 32, 64):
            rows = summary.get((k, eta, n), [])
            for (p, pl, cp, bp, bf) in rows:
                print(f"      n={n:3d} p={p:>11d}  parent_L={pl:>4} child_pairs={cp}  "
                      f"B_pair={bp}  B_F={bf}")
    print("\nNSCALE_DONE")

if __name__ == "__main__":
    run()
