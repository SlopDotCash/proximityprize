#!/usr/bin/env python3
"""
C003 follow-up: confirm the counterexamples are EXACTLY the char-p escape.

We recompute the SAME variety {S subset mu_n, |S|=a, e_1=...=e_{t-1}=0} in
CHARACTERISTIC ZERO (exact arithmetic in Z[zeta_n], the cyclotomic ring), and
compare to the count of 2^L-coset-unions C(n/2^L, a/2^L).

In char 0:  full_tower / Lam-Leung says variety == coset-unions exactly.
In char p (F_q, the prize regime): the probe C003_coset_union_exact_binomial.py
showed variety STRICTLY larger.

So the "EXACT binomial" holds in char 0 (a known/proven fact, not new) and is
FALSE over F_q. We demonstrate the char-0 equality holds for the same (n,a,t) where
char-p failed.
"""
import itertools, math
from math import comb

# Exact arithmetic in Z[zeta_n] represented as vectors of length n over Q (integers),
# with reduction by zeta_n^n = 1.  This represents char-0 cyclotomic integers.
# A primitive n-th root zeta; element = polynomial in zeta of degree < n (coeffs are ints).

def poly_mul(a, b, n):
    res = [0]*n
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj == 0: continue
            res[(i+j) % n] += ai*bj
    return res

def poly_add(a, b):
    return [x+y for x, y in zip(a, b)]

def zeta_pow(e, n):
    v = [0]*n
    v[e % n] = 1
    return v

def is_zero_cyclotomic(v, n):
    """ Is sum_i v[i] zeta^i = 0 in Z[zeta_n] (char 0)?
        Reduce modulo the n-th cyclotomic polynomial: element is 0 iff the vector
        lies in the Z-span of {zeta^j * Phi_n(zeta) reductions}.  Easiest exact test:
        evaluate the minimal polynomial relation. For n a power of 2, Phi_{2^m} = x^{n/2}+1,
        so zeta^{n/2} = -1, and {1, zeta, ..., zeta^{n/2-1}} is a Z-basis.
        Reduce: for i>=n/2, zeta^i = -zeta^{i-n/2}. Then 0 iff reduced vector is all zero. """
    half = n//2
    red = [0]*half
    for i in range(n):
        if i < half:
            red[i] += v[i]
        else:
            red[i-half] -= v[i]
    return all(x == 0 for x in red)

def esymm_cyclotomic_iszero(subset_exps, j, n):
    """ subset given as exponents e (elements zeta^e); is e_j == 0 in char 0? """
    if j == 0:
        return False  # e_0 = 1
    acc = [0]*n
    for combo in itertools.combinations(subset_exps, j):
        prod = zeta_pow(0, n)
        for e in combo:
            prod = poly_mul(prod, zeta_pow(e, n), n)
        acc = poly_add(acc, prod)
    return is_zero_cyclotomic(acc, n)

def variety_count_char0(n, a, t):
    exps = list(range(n))
    cnt = 0
    members = []
    for S in itertools.combinations(exps, a):
        ok = all(esymm_cyclotomic_iszero(S, j, n) for j in range(1, t))
        if ok:
            cnt += 1
            members.append(frozenset(S))
    return cnt, members

def coset_unions_char0(n, a, twoL):
    """ unions of (a/twoL) cosets of mu_{twoL}; cosets grouped by exponent mod (n/twoL)?
        mu_{twoL} = {zeta^{(n/twoL)*i}}. coset of x=zeta^e is {e + (n/twoL)*i mod n}. """
    if a % twoL != 0 or n % twoL != 0:
        return set()
    step = n // twoL
    # cosets keyed by e mod step
    cosets = {}
    for e in range(n):
        cosets.setdefault(e % step, set()).add(e)
    cl = [frozenset(v) for v in cosets.values()]
    assert len(cl) == step
    m = a // twoL
    res = set()
    for combo in itertools.combinations(cl, m):
        res.add(frozenset().union(*combo))
    return res

def main():
    # focus on the (n,a,t) cases that FAILED over F_q in the prior probe
    cases = [(16,4,2),(16,5,2),(16,6,2),(16,7,2),
             (8,4,2),(8,6,2),(8,4,3),(8,8,3)]
    print("n\ta\tt\t2^L\tchar0_#variety\tchar0_#cosetunions\tchar0 EQUAL?")
    all_equal = True
    for (n,a,t) in cases:
        L = 0 if t <= 1 else math.ceil(math.log2(t))
        twoL = 2**L
        vc, members = variety_count_char0(n, a, t)
        cu = coset_unions_char0(n, a, twoL)
        eq = (set(members) == cu)
        if not eq: all_equal = False
        print(f"{n}\t{a}\t{t}\t{twoL}\t{vc}\t{len(cu)}\t{eq}")
    print()
    print("char-0 variety == coset-unions in ALL tested cases:", all_equal)
    print("(=> the binomial is a CHAR-0 fact; the char-p F_q version is FALSE, per prior probe)")

if __name__ == "__main__":
    main()
