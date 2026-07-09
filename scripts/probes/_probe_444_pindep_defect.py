#!/usr/bin/env python3
"""
#444 — resolve whether the e_2=0-constrained distinct-gamma count is p-independent or
carries a char-p DEFECT (the wall). Earlier probe saw 32/16/16 at n=16,w=5 across
p=97,193,241 -> NOT identical. Question: is the variation the char-p defect (extra mod-p
collisions of distinct char-0 gammas), i.e. count(char-p) <= count(char-0) with the
DEFICIT exactly the wall? If so the binding object splits as char-0 (p-indep) MINUS defect.

We compute, over PROPER mu_n (n | p-1, n < p-1):
  N_p   = #distinct (-e_1 mod p) over S subset mu_n, |S|=w, e_2(S)=0 mod p
  N_C   = #distinct char-0 net -e_1 over S subset mu_n with char-0 e_2(S)=0
          (using exact roots of unity; e_2=0 is a complex equation)
and check N_p <= N_C (char-p collisions only shrink), and whether N_C is the stable
p-independent ceiling that N_p approaches for "generic" (large / clean) primes.
"""
from math import comb, gcd
from itertools import combinations
import cmath

def nth_root_modp(p, n):
    for cand in range(2, p):
        z = pow(cand, (p - 1) // n, p)
        if all(pow(z, d, p) != 1 for d in range(1, n)) and pow(z, n, p) == 1:
            return z
    raise RuntimeError

def mu_modp(p, n):
    z = nth_root_modp(p, n)
    return [pow(z, j, p) for j in range(n)]

def elem2(S, p):
    # e1, e2 mod p
    e1 = 0
    e2 = 0
    s1 = 0
    for x in S:
        e2 = (e2 + s1 * x) % p
        s1 = (s1 + x) % p
    e1 = s1
    return e1 % p, e2 % p

def Np(p, n, w):
    G = mu_modp(p, n)
    seen = set()
    for S in combinations(G, w):
        e1, e2 = elem2(S, p)
        if e2 == 0:
            seen.add((-e1) % p)
    return len(seen)

def Nc(n, w, tol=1e-7):
    G = [cmath.exp(2j * cmath.pi * j / n) for j in range(n)]
    seen = set()
    for S in combinations(G, w):
        e1 = sum(S)
        # e2 = sum_{i<j} x_i x_j = (e1^2 - p2)/2 ; p2 = sum x^2
        p2 = sum(x * x for x in S)
        e2 = (e1 * e1 - p2) / 2
        if abs(e2) < tol:
            seen.add((round((-e1).real, 5), round((-e1).imag, 5)))
    return len(seen)

print("=== char-p count N_p vs char-0 ceiling N_C, e_2=0 constrained, proper mu_n ===")
print("    n  w | char-0 N_C | char-p counts (several proper primes) | N_p <= N_C always?")
configs = [
    (8, 4, [97, 113, 193, 257, 337, 433, 577]),
    (8, 5, [97, 113, 193, 257, 337, 433, 577]),
    (16, 5, [97, 113, 193, 241, 337, 433, 577, 593]),
    (16, 6, [97, 113, 193, 241, 337, 433, 577, 593]),
]
for n, w, primes in configs:
    nc = Nc(n, w)
    nps = []
    for p in primes:
        if (p - 1) % n == 0 and (p - 1) != n:  # proper subgroup
            nps.append(Np(p, n, w))
    le = all(v <= nc for v in nps)
    # the MODE / max of char-p counts = the p-independent ceiling (clean primes)
    mx = max(nps)
    print(f"   {n:2d}  {w} |   {nc:5d}    | {nps}  | <=ceiling:{le}  max={mx}{'  (=N_C)' if mx==nc else ''}")
print()
print("INTERPRETATION: if N_p <= N_C with max_p N_p = N_C, the char-0 count N_C is the")
print("p-INDEPENDENT ceiling and each N_p = N_C - defect_p where defect_p>=0 is the char-p")
print("collision = the wall contribution at that prime. The OFF-BGK binding object is N_C;")
print("the BGK wall is exactly the defect. Both exceed budget structure is about N_C vs n.")
