#!/usr/bin/env python3
"""R-b recursion bijection test ONLY (fast)."""
import itertools, sys
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e
def vanishing_sets(n, p, sz, c):
    elts = subgroup(n, p)
    out = []
    for T in itertools.combinations(elts, sz):
        Tel = list(T)
        if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
            out.append(tuple(Tel))
    return out, elts

print("RECURSION BIJECTION: fully-antipodal S at (n,c) <-> vanishing S' at (n/2,c/2)", flush=True)
for (n, sz, c) in [(32,8,4),(16,8,4),(16,4,2),(32,4,2),(8,4,2)]:
    if c%2: continue
    primes = [p for p in range(n+1, 500) if isprime(p) and (p-1)%n==0][:4]
    for p in primes:
        big, elts = vanishing_sets(n, p, sz, c)
        fa = [T for T in big if all((p-x)%p in set(T) for x in T)]
        half_set = set(subgroup(n//2, p))
        recurse_ok = True; squared_images = set()
        for T in fa:
            sq = set(pow(x,2,p) for x in T)
            ok = sq.issubset(half_set) and len(sq)==sz//2 and all(sum(pow(y,j,p) for y in sq)%p==0 for j in range(1,c//2+1))
            if not ok: recurse_ok = False
            squared_images.add(frozenset(sq))
        small, _ = vanishing_sets(n//2, p, sz//2, c//2)
        small_set = set(frozenset(T) for T in small)
        bij = (squared_images == small_set)
        print(f"  n={n} s={sz} c={c} p={p}: #fully-antip={len(fa)} #total(n,c)={len(big)} "
              f"#vanish(n/2,c/2)={len(small)} recurse_valid={recurse_ok} bijective={bij}", flush=True)
