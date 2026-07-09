#!/usr/bin/env python3
"""
C034 FINAL crux: does the clean count C(n/2^L, a/2^L) survive ACCIDENTAL char-p relations?

C034's whole "floor is structural" claim rests on: the only vanishing subsets are
unions of mu_{2^L}-cosets. That is TRUE in char 0. In char p it can FAIL if there is a
low-weight {-1,0,1} additive relation among the 2^mu-th roots of unity mod q
(a 'char-p accidental' vanishing subset that is NOT a coset union).

The earlier probes used q ~ n^4..6, where such relations are absent (the #400 false-positive
trap: small/clean primes). To EXHIBIT the gap, we search for primes q = 1 mod n where the
mu_n elements DO carry a short additive relation, i.e. where some non-coset-union subset
has e_1=...=e_{t-1}=0, breaking the count formula.

If found => the count formula is a CHAR-0 identity, NOT a char-p theorem; the floor reduces
to EXACTLY the relation-free condition = the open BGK/Paley wall. (C034 = REDUCED/OPEN, welds
to wall, does NOT close.)

We do a targeted search: for n=8 and n=16, scan many primes q=1 mod n (incl. SMALL ones where
accidents are more likely, and a range), and for each test whether ANY (a,t) has
#vanishingVariety != C(n/2^L,a/2^L). Any deviation = an accidental char-p relation.
"""

import itertools, math
from math import comb

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, hi):
    out = []
    q = lo + (n - lo % n) % n + 1
    while q <= hi:
        if q % n == 1 and is_prime(q):
            out.append(q)
        q += n
    return out

def mu_n_elements(q, n):
    def order(a, q):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
            if o > q: return o
        return o
    g = None
    for cand in range(2, q):
        if order(cand, q) == q-1:
            g = cand; break
    if g is None: return None
    e = (q-1)//n
    base = pow(g, e, q)
    elts = []; x = 1
    for _ in range(n):
        elts.append(x); x = (x*base) % q
    if len(set(elts)) != n: return None
    return elts

def esymm_mod(subset, t, q):
    if t == 0: return 1 % q
    if t > len(subset): return 0
    s = 0
    for combo in itertools.combinations(subset, t):
        p = 1
        for x in combo: p = (p*x) % q
        s = (s + p) % q
    return s

def L_of(t):
    return 0 if t <= 1 else math.ceil(math.log2(t))

def count_vv(mu, a, t, q):
    cnt = 0
    for S in itertools.combinations(mu, a):
        if all(esymm_mod(S, j, q) == 0 for j in range(1, t)):
            cnt += 1
    return cnt

def scan(n, lo, hi, a_max):
    print(f"\n=== n={n}: scanning primes q=1 mod {n} in [{lo},{hi}] for count-formula DEVIATIONS ===")
    ps = primes_1_mod_n(n, lo, hi)
    print(f"  {len(ps)} primes to scan; a up to {a_max}")
    deviations = []
    for q in ps:
        mu = mu_n_elements(q, n)
        if mu is None: continue
        for a in range(2, a_max+1):
            for t in range(2, a+1):
                L = L_of(t); twoL = 2**L
                pred = comb(n//twoL, a//twoL) if (a % twoL == 0 and n % twoL == 0) else 0
                cnt = count_vv(mu, a, t, q)
                if cnt != pred:
                    deviations.append((q, a, t, cnt, pred))
                    print(f"  *** DEVIATION q={q} a={a} t={t} L={L}: actual={cnt} formula={pred} "
                          f"(accidental char-p vanishing subset!) ***")
    if not deviations:
        print(f"  no deviations in [{lo},{hi}] (formula holds; these primes are relation-free)")
    return deviations

if __name__ == "__main__":
    print("="*95)
    print("Searching for char-p accidental relations that break C034's clean count formula")
    print("="*95)
    # n=8: scan small primes (most likely to carry accidents) up to mid range; a up to 8
    d8 = scan(8, 17, 6000, 8)
    # n=16: small + mid; a up to 6 (enumeration cost)
    d16 = scan(16, 17, 12000, 6)
    print("\n"+"="*95)
    total = len(d8)+len(d16)
    if total == 0:
        print("RESULT: NO accidental relations found in scanned ranges.")
        print("  => the clean formula is robust at these (small, proper-subgroup) primes,")
        print("     BUT this is exactly the regime where accidents are ABSENT. The prize prime")
        print("     q~n*2^128 with n=2^30 is NOT testable by enumeration; whether short {-1,0,1}")
        print("     relations among 2^30-th roots vanish mod that q IS the open BGK/Paley wall.")
    else:
        print(f"RESULT: {total} accidental relations FOUND -> formula is char-0 only;")
        print("  the floor reduces to the relation-free (=BGK/Paley) condition.")
    print("="*95)
