#!/usr/bin/env python3
"""
probe_444_n16_classify_check.py  — sanity-check the coset classification at n=16.

The max-c scan reported NO non-coset defect at n=16 for any s, which is suspicious. Verify by:
  - enumerating all size-s lacunary subsets (p_1..p_c=0 mod p) at n=16 for several primes,
  - classifying each as antipodal-balanced / coset-union / OTHER (true defect),
  - so we know exactly what survives and whether the 'NO defect' is real.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e = []; x = 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def two_power_coset_unions(n, s):
    out = set()
    taus = [t for t in range(1, n+1) if n % t == 0 and (t & (t-1)) == 0]
    for tau in taus:
        if s % tau != 0:
            continue
        step = n // tau
        seen = set(); cosets = []
        for i0 in range(step):
            c = frozenset((i0 + step*j) % n for j in range(tau))
            if c not in seen:
                seen.add(c); cosets.append(c)
        need = s // tau
        if need > len(cosets):
            continue
        for combo in itertools.combinations(cosets, need):
            U = frozenset().union(*combo)
            if len(U) == s:
                out.add(U)
    return out

def is_antipodal_balanced(n, idxs):
    half = n//2; ss = set(idxs)
    return all(((i+half) % n) in ss for i in idxs)

def lacunary(n, p, s, c):
    elts = subgroup(n, p)
    powtab = [[pow(v, j, p) for j in range(1, c+1)] for v in elts]
    out = []
    for combo in itertools.combinations(range(n), s):
        ok = True
        for j in range(c):
            t = sum(powtab[i][j] for i in combo)
            if t % p != 0:
                ok = False; break
        if ok:
            out.append(frozenset(combo))
    return out

if __name__ == "__main__":
    n = 16
    print(f"### n={n} classification of lacunary subsets ###")
    primes = []
    pp = n+1
    while len(primes) < 6:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= 2:
            primes.append(pp)
        pp += n
    for s, c in [(4, 2), (6, 2), (6, 4), (8, 2), (8, 4), (8, 6)]:
        cosets = two_power_coset_unions(n, s)
        for p in primes[:4]:
            lac = lacunary(n, p, s, c)
            n_coset = sum(1 for L in lac if L in cosets)
            n_bal = sum(1 for L in lac if is_antipodal_balanced(n, L))
            # true defect = not coset AND not antipodal-balanced
            defects = [L for L in lac if (L not in cosets) and not is_antipodal_balanced(n, L)]
            # also: not-coset but balanced (these recurse per the floor)
            bal_noncoset = [L for L in lac if (L not in cosets) and is_antipodal_balanced(n, L)]
            print(f"  s={s} c={c} p={p}: |lac|={len(lac)} coset={n_coset} balanced={n_bal} "
                  f"TRUE_DEFECT={len(defects)} bal_noncoset={len(bal_noncoset)}")
            if defects:
                print(f"        defect ex: {sorted(next(iter(defects)))}")
            if bal_noncoset and s <= 8:
                print(f"        bal-noncoset ex: {sorted(bal_noncoset[0])}")
