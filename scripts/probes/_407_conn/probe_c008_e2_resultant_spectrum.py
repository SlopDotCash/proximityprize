#!/usr/bin/env python3
"""
C008 probe: Threshold-free per-instance e2=0 criterion via Res(e2Fold, Phi_{2^m}).

CLAIM (C008): "bad alpha at a=k+2  <=>  p | Res(e2Fold m A, Phi_{2^m})", a finite
divisor set per scale, "no BGK wall: the obstruction is a fixed finite arithmetic
object, not thin-subgroup cancellation".

The connection's OWN attack_plan: "a single odd factor >= n^beta is a concrete
disproof signal" (i.e. a prize-sized prime in the spectrum kills the no-BGK claim).

This probe, with EXACT integer arithmetic:
  (1) Builds e2Fold m A = canonical degree-<2^{m-1} integer rep of e2(A,zeta) mod Phi_{2^m}
      (folding X^{2^{m-1}} = -1), exactly matching the Lean e2Folded.
  (2) Computes Res(e2Fold, Phi_{2^m}) = +- N(e2(A,zeta)) (cyclotomic norm), an exact integer.
  (3) Factors it and reports: |Res|, log2|Res|, ALL odd prime factors, the LARGEST odd
      prime factor, and whether ANY odd factor reaches prize size n^beta (beta=4,5).
  (4) Sweeps n=8,16,32,64 over many subsets A (= candidate dimension exponent sets),
      reporting the WORST-CASE largest odd prime factor across A.

Honesty: we are testing whether the "finite divisor set" S(n,k) contains PRIZE-SIZED
primes (proper subgroup mu_n of F_q*, q ~ n^beta). If max odd prime factor of Res
scales like n^{c*n} (doubly exponential in the EXPONENT-COUNT), the divisor set is NOT
benign at the prize: it routinely contains primes q with mu_n a proper subgroup, and
"p | Res" at such a prime IS a bad alpha = the BGK collision. The "threshold-free"
framing does not remove the wall; it re-encodes it as "does Res have a big prime factor",
which for sparse cyclotomic integers is precisely Mahler-measure / large-prime-factor =
the open arithmetic.
"""
import sys
from sympy import factorint, Poly, symbols, isprime
from sympy import primefactors
from math import log2, comb
from itertools import combinations
import random

X = symbols('X')

def cyclotomic_2m(m):
    # Phi_{2^m}(X) = X^{2^{m-1}} + 1
    h = 2**(m-1)
    coeffs = [0]*(h+1)
    coeffs[0] = 1   # leading X^h
    coeffs[-1] = 1  # constant +1
    return coeffs  # high-to-low, degree h

def e2_folded_coeffs(m, A):
    """Exact e2Fold m A as integer coeff list, degree < 2^{m-1}.
    e2(A) = sum_{i<j in A} zeta^{i+j}; fold exponent e mod 2^m, then upper half (>=2^{m-1})
    flips sign with offset -2^{m-1} (since zeta^{2^{m-1}} = -1). Matches Lean e2Coeff."""
    n = 2**m
    h = 2**(m-1)
    coeff = [0]*h
    Al = sorted(A)
    for a in range(len(Al)):
        for b in range(a+1, len(Al)):
            e = (Al[a] + Al[b]) % n
            if e < h:
                coeff[e] += 1
            else:
                coeff[e - h] -= 1
    return coeff  # low-to-high index t, length h

def resultant_with_cyclotomic(m, A):
    """Res(e2Fold, Phi_{2^m}) exact integer = product over roots zeta of e2Fold(zeta)
    times leading-coeff factors. Equivalently the field norm N_{Q(zeta)/Q}(e2Fold(zeta))
    up to sign when e2Fold has int coeffs and Phi is monic. Use sympy resultant exactly."""
    h = 2**(m-1)
    ef = e2_folded_coeffs(m, A)        # low-to-high
    # build sympy polys
    p_ef = Poly(list(reversed(ef)), X, domain='ZZ')   # needs high-to-low
    p_cy = Poly(cyclotomic_2m(m), X, domain='ZZ')
    from sympy import resultant
    return int(resultant(p_ef.as_expr(), p_cy.as_expr(), X))

def analyze(m, A, beta_list=(4,5)):
    n = 2**m
    R = resultant_with_cyclotomic(m, A)
    if R == 0:
        return dict(R=0, char0_vanish=True)
    aR = abs(R)
    # strip powers of 2
    odd = aR
    twos = 0
    while odd % 2 == 0:
        odd //= 2
        twos += 1
    fac = factorint(odd)
    odd_primes = sorted(fac.keys())
    max_odd = max(odd_primes) if odd_primes else 1
    res = dict(
        R=R, log2_abs=log2(aR), twos=twos, is_pure_power_of_2=(odd == 1),
        odd_primes=odd_primes, max_odd_prime=max_odd, n=n,
    )
    for beta in beta_list:
        thr = n**beta
        res[f'has_prime_ge_n^{beta}'] = (max_odd >= thr)
        # also: any odd prime that is a PROPER-subgroup prime (q == 1 mod n, q prime, q > n)
    # proper-subgroup prize primes among the factors: q prime, q = 1 mod n, q >> n
    prize_primes = [p for p in odd_primes if p % n == 1 and p > n]
    res['prize_form_primes (q=1 mod n, q>n)'] = prize_primes
    res['max_prize_form_prime'] = max(prize_primes) if prize_primes else 0
    return res

def worst_case_sweep(m, sizes, n_samples=400, seed=1):
    """Over random subsets A of mu_n of given sizes, find worst-case max odd prime factor
    and worst-case log2|Res|."""
    random.seed(seed)
    n = 2**m
    universe = list(range(n))
    worst_maxodd = 1
    worst_log2 = 0.0
    worst_A = None
    worst_prizeform = 0
    worst_prize_A = None
    n_char0 = 0
    for size in sizes:
        total = comb(n, size)
        if total <= n_samples:
            iters = combinations(universe, size)
        else:
            iters = (tuple(sorted(random.sample(universe, size))) for _ in range(n_samples))
        for A in iters:
            d = analyze(m, set(A))
            if d.get('char0_vanish'):
                n_char0 += 1
                continue
            if d['max_odd_prime'] > worst_maxodd:
                worst_maxodd = d['max_odd_prime']; worst_A = (size, A)
            if d['log2_abs'] > worst_log2:
                worst_log2 = d['log2_abs']
            mp = d['max_prize_form_prime']
            if mp > worst_prizeform:
                worst_prizeform = mp; worst_prize_A = (size, A)
    return dict(m=m, n=n, sizes=list(sizes),
                worst_max_odd_prime=worst_maxodd, worst_A=worst_A,
                worst_log2_abs=worst_log2,
                worst_prize_form_prime=worst_prizeform, worst_prize_A=worst_prize_A,
                n_char0_vanish=n_char0)

if __name__ == '__main__':
    print("="*78)
    print("C008 e2-resultant spectrum probe  (EXACT integer arithmetic)")
    print("="*78)

    # Part A: sanity check against DISPROOF_LOG O141/O142 finite spectra
    # (16,8): a=10-subsets, S(16,8) max norm 18433.  Just confirm a few norms factor into S.
    print("\n[A] Sanity: e2 norms for specific n=16 subsets (compare to S(n,k) in O141)")
    for A in [ {0,1,2,3,4,5,6,7,8,9}, {0,2,4,6,8,10,12,14, 1,3} ]:
        d = analyze(4, A)
        print(f"  A(|A|={len(A)})  log2|Res|={d['log2_abs']:.1f}  "
              f"max_odd={d['max_odd_prime']}  odd_primes(<=2000)={[p for p in d['odd_primes'] if p<=2000]}")

    # Part B: the prize-regime question — does the worst-case largest odd prime factor of
    # Res grow doubly-exponentially, so that prize-sized primes (q ~ n^4..n^5, q=1 mod n,
    # mu_n a PROPER subgroup) appear in the divisor set?
    print("\n[B] Worst-case largest ODD prime factor of Res(e2Fold, Phi_{2^m}) over subsets A")
    print("    (prize: q ~ n^beta, q=1 mod n, mu_n proper subgroup; need max-odd vs n^4,n^5)")
    for (m, sizes, ns) in [
        (3, [2,3,4,5,6,7], 0),          # n=8 exhaustive-ish
        (4, [3,5,8,10,12], 300),        # n=16
        (5, [4,8,12,16,20], 200),       # n=32
        (6, [6,12,18,24,32], 80),       # n=64
    ]:
        w = worst_case_sweep(m, sizes, n_samples=ns if ns else 100000)
        n = w['n']
        print(f"\n  n={n} (m={m}):")
        print(f"    worst log2|Res|         = {w['worst_log2_abs']:.1f}   "
              f"(n^4={n**4}=2^{4*m}, n^5={n**5}=2^{5*m})")
        print(f"    worst max ODD prime     = {w['worst_max_odd_prime']}  "
              f"(= 2^{log2(max(w['worst_max_odd_prime'],1)):.1f})")
        print(f"    worst PRIZE-FORM prime  = {w['worst_prize_form_prime']}  "
              f"(q=1 mod {n}, q>n; this q would have mu_{n} as PROPER subgroup)")
        if w['worst_prize_form_prime']:
            print(f"        -> witnessed at A = {w['worst_prize_A']}")
        print(f"    n^4 = {n**4} (2^{4*m}), n^5 = {n**5} (2^{5*m})")
        print(f"    max-odd >= n^4 ? {w['worst_max_odd_prime'] >= n**4} ;  "
              f">= n^5 ? {w['worst_max_odd_prime'] >= n**5}")
