#!/usr/bin/env python3
"""
R-b POINT (ii) + hunt for multi-odd-condition free cores.

(A) RECURSION TEST: for fully-antipodal vanishing-S at (n, c), verify the squared half
    S' = {x^2 : x in S}  (size s/2) is a subset of mu_{n/2} with the FIRST c/2 power sums
    vanishing mod p.  And check the count consistency:
       #{fully-antipodal S at (n,c)}  vs  #{vanishing-S' at (n/2, c/2)} * (lift multiplicity).
    Each S' lifts to exactly one fully-antipodal S (S = preimage under squaring = S' union -S').
    So the map S -> S' should be a BIJECTION fully-antipodal(n,c) <-> vanishing(n/2,c/2).

(B) HUNT: search larger n (n=32,64) and a wide c for ANY free-core defect with ceil(c/2)>=2,
    using a NORM-FIRST filter: we want |C| reasonably large so the constraint is satisfiable.
    Then check v_p(N(beta_C)) vs ceil(c/2).
"""
import itertools
from sympy import isprime, primitive_root, symbols, Poly, resultant, cyclotomic_poly, ZZ
from collections import Counter

_X = symbols('x')
def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e
def exact_norm_int(idxs, n):
    cnt = Counter(i % n for i in idxs)
    Bpoly = Poly(sum(co*_X**e for e, co in cnt.items()), _X, domain=ZZ)
    Phi = Poly(cyclotomic_poly(n, _X), _X, domain=ZZ)
    return int(resultant(Phi, Bpoly))
def vp(N, p):
    if N == 0: return "ZERO"
    v, a = 0, abs(int(N))
    while a % p == 0:
        a //= p; v += 1
    return v
def vanishing_sets(n, p, sz, c):
    elts = subgroup(n, p)
    out = []
    for T in itertools.combinations(elts, sz):
        Tel = list(T)
        if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
            out.append(tuple(Tel))
    return out, elts

print("="*88)
print("(A) RECURSION BIJECTION TEST: fully-antipodal S at (n,c) <-> vanishing S' at (n/2,c/2)")
print("="*88)
for (n, sz, c) in [(32,8,4),(16,8,4),(16,4,2),(32,12,4),(32,4,2)]:
    if c%2 != 0: continue
    primes = [p for p in range(n+1, 800) if isprime(p) and (p-1)%n==0][:4]
    for p in primes:
        big, elts = vanishing_sets(n, p, sz, c)
        idxmap = {x:i for i,x in enumerate(elts)}
        # fully-antipodal subset
        fa = [T for T in big if all((p-x)%p in set(T) for x in T)]
        # square map: x -> x^2 ; lands in mu_{n/2}
        half_elts = subgroup(n//2, p)
        half_set = set(half_elts)
        recurse_ok = True
        squared_images = set()
        for T in fa:
            sq = set(pow(x,2,p) for x in T)
            # check sq subset of mu_{n/2}, size sz/2, and first c/2 power sums vanish
            cond1 = sq.issubset(half_set)
            cond2 = (len(sq)==sz//2)
            cond3 = all(sum(pow(y,j,p) for y in sq)%p==0 for j in range(1,c//2+1))
            if not (cond1 and cond2 and cond3):
                recurse_ok = False
            squared_images.add(frozenset(sq))
        small, _ = vanishing_sets(n//2, p, sz//2, c//2)
        small_set = set(frozenset(T) for T in small)
        bij = (squared_images == small_set)
        print(f"  n={n} s={sz} c={c} p={p}: #fully-antipodal={len(fa)}  #vanishing(n/2={n//2},c/2={c//2})={len(small)}  "
              f"recurse_valid={recurse_ok}  square-map-bijective={bij}")

print("\n"+"="*88)
print("(B) HUNT free-core defect with ceil(c/2)>=2 at larger n  (exponent stress test)")
print("="*88)
import sys
found_any = False
for (n, sz, c) in [(32,10,4),(32,12,4),(32,11,3),(32,9,3),(64,10,4),(64,12,4)]:
    need = (c+1)//2
    if need < 2: continue
    primes = [p for p in range(n+1, 400) if isprime(p) and (p-1)%n==0][:3]
    for p in primes:
        elts = subgroup(n, p); im = {x:i for i,x in enumerate(elts)}
        cnt_fc = 0
        seen = set()
        for T in itertools.combinations(elts, sz):
            Tel = list(T); Tset = set(Tel)
            if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
                core = [x for x in Tel if (p-x)%p not in Tset]
                if not core: continue
                key = tuple(sorted(im[x] for x in core))
                if key in seen: continue
                seen.add(key); cnt_fc += 1
                idxs = list(key)
                N = exact_norm_int(idxs, n)
                v = vp(N, p)
                short = isinstance(v,int) and v < need
                found_any = True
                flag = "  <<<<< SHORT!!" if short else ""
                print(f"  n={n} s={sz} c={c} need={need} p={p}: |C|={len(core)} v_p(N)={v} N={N}{flag}")
                if cnt_fc > 8: break
        sys.stdout.flush()
if not found_any:
    print("  (still no free-core defect with ceil(c/2)>=2 found)")
