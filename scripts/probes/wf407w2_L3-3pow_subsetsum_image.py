#!/usr/bin/env python3
"""
wf407w2_L3-3pow_subsetsum_image.py  --  #407 thread L3-3pow.

EXACT char-0 subset-sum IMAGE size of the index-2 subgroup mu_{n/2} of mu_n, and the
companion full-group mu_n count.  Confirms the Wave-1 (T09) measurement:

    | { sum over S : S subseteq mu_{n/2} } |  =  3^{n/4}    (the SET of distinct subset sums)

Mechanism (to verify, not assume):
  * mu_{n/2} (order n/2) sits on the unit circle (n/2 = 2^{mu-1}-th roots of unity in C);
    it has h = (n/2)/2 = n/4 ANTIPODAL PAIRS {zeta, -zeta} (because -1 = zeta^{(n/2)/2} is in
    mu_{n/2} when n/2 is even, i.e. mu>=2).
  * A subset S of mu_{n/2} picks, per antipodal pair, one of {include zeta, include -zeta,
    include both, include neither}.  The SUM only sees the antipodal-reduced contribution:
      both -> zeta + (-zeta) = 0 ;  neither -> 0 ;  only zeta -> +zeta ;  only -zeta -> -zeta.
    So each pair contributes a coefficient eps in {-1, 0, +1} to  sum = Σ_{pairs} eps_j * zeta_j.
  * Φ_{n/2}(X) = X^{n/4} + 1 (since n/2 = 2^mu' is a 2-power) is the minimal polynomial of zeta,
    degree n/4 = h, so {1, zeta, ..., zeta^{h-1}} are LINEARLY INDEPENDENT over Q
    ==> the map eps in {-1,0,1}^h |-> Σ eps_j zeta_j is INJECTIVE
    ==> # distinct subset sums = |{-1,0,1}^h| = 3^h = 3^{n/4}.

We verify EXACTLY (no sampling):
  (A) char-0: enumerate every subset of mu_{n/2} as exact cyclotomic integers, count distinct sums.
      Compare to 3^{n/4} and to the box bound 2^{n/2}.
  (B) char-0 full group mu_n: count distinct subset sums; compare to 3^{n/2}.
  (C) char-p (large prime p = 1 mod n): same enumeration mod p; confirm equals char-0 (no extra
      coincidences when p large), i.e. 3^{n/4} survives the transfer at large p.
  (D) the stratum law:  Σ_{a=0}^{h} 2^a C(h,a) = 3^h  (the in-tree subsetSumSpectrum_card with
      A = {0..h}); print the per-weight strata and the running total.
"""
import math
from itertools import combinations
from collections import defaultdict


# ---------- exact cyclotomic-integer arithmetic in Z[zeta_N], zeta_N = exp(2 pi i / N) ----------
# Represent an element of Z[zeta_N] as a tuple of N integer coefficients (the "naive" basis
# 1, zeta, ..., zeta^{N-1}); reduce zeta^k for k>=N via zeta^N = 1.  For DISTINCTNESS of sums
# of subgroup roots-of-unity this naive (possibly non-reduced) representation is fine BECAUSE
# every term is exactly some zeta^k with k < N, so sums are honest length-N integer vectors and
# two sums are equal as algebraic numbers IFF ... not quite (1 + zeta + ... relations).  To be
# fully rigorous we reduce modulo the cyclotomic relation by mapping to the basis of degree
# < phi(N).  Simplest exact route: evaluate each algebraic number by its full minimal-data
# fingerprint = the coefficient vector in the power basis reduced mod Phi_N.  For N a 2-power,
# Phi_N(X) = X^{N/2} + 1, so reduce: zeta^{N/2 + j} = - zeta^j.  That gives a canonical
# length-(N/2) integer vector; equality of vectors <=> equality of algebraic numbers (since
# {1,...,zeta^{N/2-1}} is a Z-basis of Z[zeta_N] for N a 2-power).

def reduce_2power(coeffs, N):
    """coeffs: list length N (coefficient of zeta^k).  N a power of 2.  Return canonical
    length-(N/2) tuple in the power basis using zeta^{N/2+j} = -zeta^j (Phi_N = X^{N/2}+1)."""
    h = N // 2
    out = [0] * h
    for k, c in enumerate(coeffs):
        if c == 0:
            continue
        kk = k % N
        if kk < h:
            out[kk] += c
        else:
            out[kk - h] -= c
    return tuple(out)


def roots_of_unity_indices(N, order):
    """Indices k (in 0..N-1) of the elements of the subgroup of order `order` inside mu_N.
    The subgroup of order d = mu_d = { zeta_N^{ (N/d) * t } : t = 0..d-1 }."""
    step = N // order
    return [(step * t) % N for t in range(order)]


def exact_subset_sum_image_count(N, order):
    """EXACT count of distinct subset sums of the order-`order` subgroup of mu_N (char 0),
    via canonical 2-power cyclotomic reduction.  Returns (#distinct, #subsets)."""
    idxs = roots_of_unity_indices(N, order)
    seen = set()
    n = len(idxs)
    # enumerate all 2^n subsets
    for mask in range(1 << n):
        coeffs = [0] * N
        m = mask
        i = 0
        while m:
            if m & 1:
                coeffs[idxs[i]] += 1
            m >>= 1
            i += 1
        seen.add(reduce_2power(coeffs, N))
    return len(seen), (1 << n)


def is_prime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d = m - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def smallest_prime_1_mod(n, lo):
    p = lo + ((1 - lo) % n)
    if p < 3:
        p += n
    while True:
        if p % n == 1 and is_prime(p):
            return p
        p += n


def factorize(m):
    s = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            s[d] = s.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        s[m] = s.get(m, 0) + 1
    return s


def primitive_root(p):
    fac = factorize(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    return None


def charp_subset_sum_image_count(p, order):
    """EXACT count of distinct subset sums of the order-`order` subgroup mu_order < F_p^*,
    computed in F_p (no sampling)."""
    g = primitive_root(p)
    h = pow(g, (p - 1) // order, p)          # generator of the order-`order` subgroup
    elems = [pow(h, t, p) for t in range(order)]
    seen = set()
    n = len(elems)
    for mask in range(1 << n):
        s = 0
        m = mask
        i = 0
        while m:
            if m & 1:
                s = (s + elems[i]) % p
            m >>= 1
            i += 1
        seen.add(s)
    return len(seen), (1 << n)


def main():
    print("=" * 100)
    print("L3-3pow : EXACT char-0 subset-sum image of the index-2 subgroup mu_{n/2}  =>  3^{n/4}")
    print("=" * 100)

    # (A)+(B): char-0 exact counts.  n = 8, 16, 32; subgroup order = n/2 (index-2) and full n.
    print("\n(A/B) char-0 exact subset-sum image sizes (canonical cyclotomic reduction):")
    print(f"  {'n':>4} {'subgrp':>8} {'order':>6} {'h(pairs)':>9} "
          f"{'#distinct':>11} {'2^order(box)':>13} {'3^h':>10} {'match 3^h':>10}")
    for n in (8, 16, 32):
        for label, order in (("mu_{n/2}", n // 2), ("mu_n", n)):
            # full group mu_n for n=32 is 2^32 subsets -> too big; only do small ones
            if order > 18:
                print(f"  {n:>4} {label:>8} {order:>6} {order//2:>9} "
                      f"{'(skip: 2^'+str(order)+' subsets)':>11}")
                continue
            cnt, nsub = exact_subset_sum_image_count(n, order)
            h = order // 2
            three_h = 3 ** h
            box = 2 ** order
            ok = "YES" if cnt == three_h else "NO"
            print(f"  {n:>4} {label:>8} {order:>6} {h:>9} "
                  f"{cnt:>11} {box:>13} {three_h:>10} {ok:>10}")

    # Headline reproduction the task asks for: half = 4, 8, 16  (i.e. n/2 = 4,8,16 => n=8,16,32)
    print("\n  HEADLINE (task parts 1+2): subgroup order = n/2 = 4, 8, 16:")
    for order in (4, 8, 16):
        n = 2 * order
        cnt, _ = exact_subset_sum_image_count(n, order)
        h = order // 2
        print(f"    n/2={order:>3} (n={n:>3}, h=n/4={h}):  image size = {cnt:>6}  "
              f"= 3^{h} = {3**h}  -> {'EXACT MATCH' if cnt == 3**h else 'MISMATCH!!'}")

    # (C): char-p transfer at large prime: same count survives.
    print("\n(C) char-p exact subset-sum image of mu_{n/2} at large primes (transfer check):")
    print(f"  {'n':>4} {'order=n/2':>10} {'beta':>5} {'p':>12} "
          f"{'#distinct(F_p)':>15} {'3^{n/4}':>10} {'survives':>9}")
    for n in (8, 16):
        order = n // 2
        h = order // 2
        target = 3 ** h
        for beta in (2.0, 3.0, 4.0, 5.0):
            p = smallest_prime_1_mod(n, int(n ** beta))
            cnt, _ = charp_subset_sum_image_count(p, order)
            print(f"  {n:>4} {order:>10} {beta:>5} {p:>12} "
                  f"{cnt:>15} {target:>10} {'YES' if cnt == target else 'collapsed':>9}")

    # (D): the stratum law  sum_{a=0}^{h} 2^a C(h,a) = 3^h
    print("\n(D) stratum decomposition  N = sum_{a=0}^{h} 2^a*C(h,a) = 3^h  (in-tree spectrum law):")
    for order in (4, 8, 16):
        h = order // 2
        total = 0
        parts = []
        for a in range(h + 1):
            term = (2 ** a) * math.comb(h, a)
            total += term
            parts.append(term)
        print(f"    h=n/4={h:>2}: strata {parts}  sum={total} = 3^{h} = {3**h}  "
              f"-> {'OK' if total == 3**h else 'BAD'}")

    print("\n" + "=" * 100)
    print("VERDICT: subset-sum image of the index-2 subgroup mu_{n/2} is EXACTLY 3^{n/4} in char 0,")
    print("and survives unchanged mod a large prime p (no extra coincidences).  Mechanism = each of")
    print("the h=n/4 antipodal pairs contributes eps in {-1,0,1}; injectivity from Phi_{n/2}=X^{n/4}+1.")
    print("This is subsetSumSpectrum_card with A={0..h}: sum 2^a C(h,a) = 3^h, sharper than the 2^{n/2} box.")


if __name__ == "__main__":
    main()
