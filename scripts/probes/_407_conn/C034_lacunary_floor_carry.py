#!/usr/bin/env python3
"""
C034 probe: "L must straddle k: lacunary floor FALSE-risk only at 2-adic carry resonance".

Claim to test (from C034.json), for the DYADIC subgroup mu_n (n=2^mu) inside F_q*:

  vanishingVariety(mu_n, a, t) = { S subset mu_n : |S|=a, e_1(S)=...=e_{t-1}(S)=0 }

C034 asserts (via lacunary L=ceil(log2 t)):
  (A) vanishingVariety(mu_n, k+t, t) is NONEMPTY  iff  2^L | (k+t).
  (B) at resonant t, count = C(n/2^L, (k+t)/2^L).

NOTE the structural subtlety we must check: the in-tree lemma card_le_gcd_of_esymm_zero
applies only when ALL e_1..e_{a-1} vanish (h=|S|=a). The vanishingVariety only kills
e_1..e_{t-1} with t < a in general. So the lemma does NOT directly give claim (A).
We test (A)/(B) directly by EXACT brute-force enumeration over real mu_n in real F_q.

We use exact integer arithmetic mod q. We enumerate subsets of mu_n of size a and test
e_1=...=e_{t-1}=0 mod q. n kept small (8,16) so a-subsets are enumerable.

PRIZE-FAITHFUL field choice: q prime, q = 1 mod n, n=2^mu a PROPER subgroup, q ~ n^beta
(beta 4-5), large prime, several primes. Full-group is the #400 trap (excluded).
"""

import itertools, math
from math import comb, gcd

def find_primes(n, count, beta_lo=4, beta_hi=6):
    """Primes q = 1 mod n with q ~ n^beta, beta in [beta_lo,beta_hi], proper subgroup."""
    def is_prime(m):
        if m < 2: return False
        if m % 2 == 0: return m == 2
        i = 3
        while i*i <= m:
            if m % i == 0: return False
            i += 2
        return True
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    out = []
    # start a bit above lo to be safe, step by n
    start = lo + (n - lo % n) % n + 1  # = 1 mod n region
    q = start
    while q <= hi and len(out) < count:
        if q % n == 1 and is_prime(q):
            out.append(q)
        q += n
    return out

def mu_n_elements(q, n):
    """The n-th roots of unity in F_q (q = 1 mod n): {g^(j*(q-1)/n)} for a generator g."""
    # find a generator of F_q^*
    def order(a, q):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
        return o
    # find generator
    g = None
    for cand in range(2, q):
        if order(cand, q) == q-1:
            g = cand; break
    assert g is not None
    e = (q-1)//n
    base = pow(g, e, q)  # primitive n-th root
    elts = []
    x = 1
    for _ in range(n):
        elts.append(x)
        x = (x*base) % q
    assert len(set(elts)) == n, "mu_n not distinct"
    return elts

def esymm_mod(subset, t, q):
    """e_t of a subset (list of field elements) mod q, via sum over t-subsets products."""
    if t == 0: return 1 % q
    if t > len(subset): return 0
    s = 0
    for combo in itertools.combinations(subset, t):
        p = 1
        for x in combo: p = (p*x) % q
        s = (s + p) % q
    return s

def count_vanishing_variety(mu, a, t, q):
    """Exact count of size-a subsets S of mu with e_1(S)=...=e_{t-1}(S)=0 mod q."""
    cnt = 0
    for S in itertools.combinations(mu, a):
        ok = True
        for j in range(1, t):
            if esymm_mod(S, j, q) != 0:
                ok = False; break
        if ok:
            cnt += 1
    return cnt

def L_of(t):
    return 0 if t <= 1 else math.ceil(math.log2(t))

def predict(n, a, t):
    """C034 prediction: nonempty iff 2^L | a (here a=k+t); count = C(n/2^L, a/2^L)."""
    L = L_of(t)
    twoL = 2**L
    if a % twoL != 0:
        return 0, L, twoL
    if n % twoL != 0:
        return 0, L, twoL  # cannot even form
    return comb(n // twoL, a // twoL), L, twoL

def run():
    print("="*100)
    print("C034 probe: lacunary floor / 2-adic carry resonance")
    print("="*100)
    mismatchesA = 0  # nonemptiness sign mismatches
    mismatchesB = 0  # count mismatches at resonance
    total = 0
    for n in [8, 16]:
        primes = find_primes(n, 3)
        print(f"\nn=2^{int(math.log2(n))}={n}  primes (q=1 mod n, q~n^4..6): {primes}")
        for q in primes:
            mu = mu_n_elements(q, n)
            # iterate a from small to n, t from 2..a (t>=2 means at least e_1=0 constraint)
            for a in range(2, n+1):
                for t in range(2, a+1):
                    cnt = count_vanishing_variety(mu, a, t, q)
                    pred, L, twoL = predict(n, a, t)
                    total += 1
                    # Claim A: nonemptiness sign
                    actual_nonempty = (cnt > 0)
                    pred_nonempty = (pred > 0)
                    tagA = ""
                    if actual_nonempty != pred_nonempty:
                        mismatchesA += 1
                        tagA = "  <-- A MISMATCH (nonemptiness)"
                    tagB = ""
                    if actual_nonempty and pred_nonempty and cnt != pred:
                        mismatchesB += 1
                        tagB = "  <-- B MISMATCH (count)"
                    # only print interesting rows: nonempty actual OR predicted, or any mismatch
                    if actual_nonempty or pred_nonempty or tagA:
                        print(f"  q={q} a={a} t={t} L={L} 2^L={twoL} | "
                              f"actual_cnt={cnt} pred(C({n}/{twoL},{a}/{twoL}))={pred}"
                              f"{tagA}{tagB}")
    print("\n" + "="*100)
    print(f"TOTAL cases: {total}")
    print(f"Claim A (nonemptiness iff 2^L|(k+t)) mismatches: {mismatchesA}")
    print(f"Claim B (count = C(n/2^L,(k+t)/2^L)) mismatches at resonance: {mismatchesB}")
    print("="*100)

if __name__ == "__main__":
    run()
