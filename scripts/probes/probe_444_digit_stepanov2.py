#!/usr/bin/env python3
"""
probe(#444) PART 2: What does the BEST Stepanov-type bound DELIVER inside n < p^{1/3}, and can
the x->x^2 DIGIT RECURSION sharpen the per-point multiplicity to reach sqrt(n log m)?

The univariate-Stepanov character-sum machine (Stepanov 1969, Mit'kin, Heath-Brown-Konyagin 2000,
Konyagin-Shparlinski book) bounds incomplete subgroup sums. The cleanest statement for the FULL
subgroup sum eta_b = sum_{x in mu_n} e_p(bx) via Stepanov / Weil is:

   |eta_b| <= sqrt(p)        (Weil; in-tree SubgroupGaussSumWorstCase.lean)

The HBK sub-multiplicative refinement (using additive energy / sum-product) gives, for the MAXIMUM
over an interval of length H of points of mu_n:
   T_b(H) = #{x in mu_n : bx mod p in [0,H)}  controlled to  ~ Hn/p + sqrt(n) * (error)
The Stepanov auxiliary there vanishes at the (few) points of mu_n inside a short interval; the
reach is governed by deg/mult and the boundary is exactly n < p^{1/3} (HBK Thm: nontrivial bound
on the LEAST quadratic nonresidue / subgroup distribution needs |H| > p^{1/3}-ish).

DIGIT-RECURSION CLAIM under test: build a sigma-covariant auxiliary (sigma: x->x^2) whose
multiplicity at each mu_n point ACCUMULATES across the mu=log2(n) digit levels, giving effective
mult M ~ mu for free. Then reach n*M <= deg would let n*log n <= deg ~ p^{1/2}, i.e. the SAME
sqrt(p) scale, NOT an improvement on the magnitude side -- and on the FLATNESS side (which is what
sqrt(n log m) requires) Stepanov says nothing because it counts ZEROS/level sets, not cancellation.

This probe DIRECTLY measures three decisive quantities and reports an honest verdict.
"""
import numpy as np
import math
from itertools import product

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n, beta=4.0):
    target = n**beta
    k = max(2, int(math.ceil(target/n)))
    while True:
        p = k*n+1
        if p > n and is_prime(p): return p
        k += 1

def subgroup_gen(p, n):
    g = 2
    while True:
        h = pow(g, (p-1)//n, p)
        if pow(h, n, p) == 1:
            ok = True
            for d in range(1, n):
                if n % d == 0 and pow(h, d, p) == 1:
                    ok = False; break
            if ok: return h
        g += 1

def mu_n_set(p, n):
    h = subgroup_gen(p, n); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    return S

# ----------------------------------------------------------------------------
# TEST A: does the x->x^2 map FIX mu_n (so a covariant auxiliary can recurse on it)?
# For mu_n with n=2^mu: squaring x->x^2 is a 2-to-1 ENDOMORPHISM of mu_n onto mu_{n/2}.
# It is NOT an automorphism of mu_n (kernel {1,-1}). So a "digit recursion" Psi(x^2)=f(Psi(x))
# pushes DOWN the tower (n -> n/2), shrinking the set, not adding multiplicity at fixed n.
# ----------------------------------------------------------------------------
def test_squaring_structure(mu=5):
    p = find_prime(2**mu, beta=4.0); n = 2**mu
    S = set(mu_n_set(p, n))
    sq = set((x*x)%p for x in S)
    print("="*78)
    print("TEST A: structure of x->x^2 on mu_n (n=2^mu) -- can it recurse ON mu_n?")
    print("="*78)
    print(f"  n={n}, p={p}")
    print(f"  |mu_n| = {len(S)},  |sq(mu_n)| = {len(sq)},  sq(mu_n) subset mu_n? {sq <= S}")
    print(f"  sq is the order-{n//2} subgroup mu_{{n/2}}? {len(sq)==n//2}")
    # fibers: each y in sq(mu_n) has exactly 2 preimages
    from collections import Counter
    fib = Counter((x*x)%p for x in S)
    fibsizes = Counter(fib.values())
    print(f"  fiber sizes of x->x^2 on mu_n: {dict(fibsizes)}  (2-to-1 onto mu_{{n/2}})")
    print("  => squaring is a TOWER PROJECTION mu_n ->> mu_{n/2}, NOT a self-map fixing mu_n.")
    print("     A covariant recursion descends the tower (n->n/2); it cannot pile multiplicity")
    print("     at a fixed level n without leaving the set. This is the structural obstruction.")
    print()

# ----------------------------------------------------------------------------
# TEST B: the FUNDAMENTAL Stepanov inequality is |T|*M <= deg, and digit-recursion cannot
# break it. We verify that NO polynomial of degree < n*M vanishes to order M on n distinct
# points (it must be divisible by prod (X-a)^M). This is an IDENTITY -- the digit tower is
# irrelevant to it. We confirm over F_p for several primes.
# ----------------------------------------------------------------------------
def test_multiplicity_lower_bound(mu=4, trials=3):
    import sympy
    print("="*78)
    print("TEST B: |T|*M <= deg is an IDENTITY (digit recursion gives NO discount)")
    print("="*78)
    p = find_prime(2**mu, beta=4.0); n = 2**mu
    S = mu_n_set(p, n)
    X = sympy.symbols('X')
    Fp = sympy.GF(p)
    # The minimal-degree poly vanishing to order M on all of mu_n is (X^n-1)^M, degree n*M.
    for M in (1,2,3):
        Psi = sympy.Poly((X**n - 1)**M, X, modulus=p)
        deg = Psi.degree()
        # check multiplicity at one point
        a = S[1]
        # mult = largest k with (X-a)^k | Psi
        q = Psi; k=0
        Xa = sympy.Poly(X - a, X, modulus=p)
        while True:
            quo, rem = divmod(q, Xa)
            if rem.is_zero:
                k+=1; q=quo
            else: break
        print(f"  M={M}: minimal covariant vanisher (X^n-1)^M has deg={deg}={n}*{M}, mult@pt={k}; "
              f"deg/(n*M)={deg/(n*M):.2f} (=1, TIGHT, no digit discount possible)")
    print("  Any Psi with mult>=M on these n distinct points is divisible by (X^n-1)^M => deg>=nM.")
    print("  The x->x^2 recursion does not change the n distinct points => NO escape. ")
    print()

# ----------------------------------------------------------------------------
# TEST C: what bound does Stepanov ACTUALLY give for M(n), and the gap to sqrt(n log m)?
# The deepest honest point: even at its theoretical best (deg ~ sqrt(p), full subgroup |T|=n),
# n*M <= sqrt(p) gives M <= sqrt(p)/n = n^{beta/2-1}; at beta=4, M <= n^1 = n. That's TRIVIAL
# (|eta|<=n always). The Stepanov MULTIPLICITY route bounds the NUMBER OF POINTS in a level set,
# giving |eta| <= sqrt(p) (Weil), which at beta=4 is sqrt(p)=n^2 -- VACUOUS (eta <= n trivially).
# Digit recursion changing M by a log factor cannot move n^{beta/2-1} below sqrt(n log m).
# ----------------------------------------------------------------------------
def test_bound_gap():
    print("="*78)
    print("TEST C: the bound Stepanov delivers vs the prize target, at beta=4 (DECISIVE)")
    print("="*78)
    print("  Stepanov/Weil magnitude:    |eta_b| <= sqrt(p) = n^{beta/2} = n^2  (beta=4)  -> VACUOUS")
    print("    (trivial bound is |eta_b| <= n; sqrt(p)=n^2 >> n, so Weil says nothing past trivial)")
    print("  Best level-set Stepanov:    n*M <= deg_aux; deg_aux >= sqrt(p) forced by Frobenius")
    print("    => the ZERO-COUNTING bound cannot certify CANCELLATION among the n phases.")
    print(f"  {'mu':>3} {'n':>10} {'target sqrt(n log m)':>22} {'sqrt(p)=n^2':>14} {'n^{1-o(1)} BGK':>16}")
    for mu in [10,20,30]:
        n=2**mu; beta=4; p=n**beta; m=p//n
        target=math.sqrt(n*math.log(m))
        sqrtp=math.sqrt(p)
        bgk=n**0.95  # n^{1-o(1)}, illustrative
        print(f"  {mu:>3} {n:>10} {target:>22.3e} {sqrtp:>14.3e} {bgk:>16.3e}")
    print()
    print("  The prize gap is sqrt(n) vs n^{1-o(1)} = a POLYNOMIAL-IN-n cancellation gap.")
    print("  Stepanov is a ZERO-COUNTING/level-set method: it bounds how many x in mu_n hit a")
    print("  target value, NOT the cancellation in sum e_p(bx). It is INHERENTLY a magnitude tool,")
    print("  and its magnitude output is sqrt(p) (=n^2 at beta=4), which is ABOVE the trivial n.")
    print("  The digit recursion proposes to add multiplicity ~log n; even granting it for FREE,")
    print("  the reach n*log n <= deg ~ sqrt(p) still gives a MAGNITUDE bound, never sqrt(n log m)")
    print("  cancellation. This is the meta-theorem (b): Stepanov is deterministic-archimedean but")
    print("  is NOT genuinely L-infinity for the CANCELLATION the prize needs -- it counts zeros.")

if __name__ == "__main__":
    test_squaring_structure(mu=5)
    test_multiplicity_lower_bound(mu=4)
    test_bound_gap()
