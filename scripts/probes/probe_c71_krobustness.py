#!/usr/bin/env python3
"""
#444 door-(iv) — is the C71 multi-term DOMINANCE gap (s23max > s1max) robust in k, or a k=2 artifact?

C71SparseOrbitGap (5dd3a409e) and the coeff-interference follow-ons (3591ed7c8/769d6177f/73575c7e9)
established at n=8, k=2 that the worst <=3-sparse adversary is STRICTLY multi-term (s23max=9 > s1max=8).
This probe stresses the k-axis: does that strict dominance persist at k=3?

EXACT full-alpha-sweep bad-strength, EXACT max-agreement-to-RS, thin mu_n n=8, Johnson agreement
thr=ceil(sqrt(k/n)*n), NEVER n=q-1, p in {17,41}, exhaustive over ALL <=3-term supports, with
unit + non-unit coeff choices (since the worst case is a coeff-interference object).

FINDING (this harness, recorded in DISPROOF_LOG [door-iv-c71-dominance-k2-specific]):
  k=2: s1max=8, s23max=9  => gap = +1 (strict multi-term dominance)
  k=3: s1max=8, s23max=8  => gap =  0 (monomial TIES; strict dominance VANISHES)
The strict s23>s1 dominance is k=2-specific at n=8. HOWEVER the [T4] coefficient-interference signal
PERSISTS at k=3 (only 3/13 and 4/18 winning (support,coeff) pairs use unit coeffs), so even where
monomials tie, the multi-term worst case is still attained predominantly at non-unit ratios.
"""
import itertools, random
from math import sqrt, ceil
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out = []; p = (lo | 1)
    while len(out) < cap:
        if (p - 1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out

def prime_factors(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0: fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def root_of_unity(p, n):
    g = 2
    while True:
        w = pow(g, (p-1)//n, p)
        if w != 1 and pow(w, n, p) == 1 and all(pow(w, n//q, p) != 1 for q in prime_factors(n)):
            return w
        g += 1

def max_agreement_to_RS(v, dom, k, p):
    n = len(dom); best = 0
    for S in itertools.combinations(range(n), k):
        xs = [dom[i] for i in S]; ys = [v[i] for i in S]; agree = 0
        for jj in range(n):
            xq = dom[jj]; num = 0
            for a in range(k):
                term = ys[a]; xa = xs[a]
                for b in range(k):
                    if b == a: continue
                    term = term * ((xq - xs[b]) % p) % p * pow((xa - xs[b]) % p, p-2, p) % p
                num = (num + term) % p
            if num == v[jj]: agree += 1
        if agree > best:
            best = agree
            if best == n: break
    return best

def bad_strength(fvals, dom, k, p, thr, g0):
    n = len(dom); bad = 0
    for alpha in range(1, p):
        v = [(g0[j] + alpha*fvals[j]) % p for j in range(n)]
        if max_agreement_to_RS(v, dom, k, p) >= thr: bad += 1
    return bad

def evalf(coeffs, dom, p):
    return [sum(c*pow(x,e,p) for e,c in coeffs.items()) % p for x in dom]

def run(n, plist, k):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson-agreement thr={thr}/{n} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        g0 = evalf({k+1: 1}, dom, p)
        s1 = 0
        for b in range(1, n):
            s1 = max(s1, bad_strength(evalf({b:1}, dom, p), dom, k, p, thr, g0))
        s23 = 0; winners = []
        for s in (2, 3):
            for supp in itertools.combinations(range(1, n), s):
                for cp in ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1), [1]+[3]*(s-1)):
                    fv = evalf({supp[i]: cp[i] for i in range(s)}, dom, p)
                    if all(x==0 for x in fv): continue
                    st = bad_strength(fv, dom, k, p, thr, g0)
                    if st > s23: s23 = st; winners = [(supp, tuple(cp))]
                    elif st == s23 and st > 0: winners.append((supp, tuple(cp)))
        unit_wins = sum(1 for _,c in winners if set(c) == {1})
        gap = s23 - s1
        verdict = "STRICT multi-term dominance" if gap > 0 else "dominance VANISHES (monomial ties/wins)"
        print(f"  p={p}: s1max={s1} s23max={s23} gap={gap:+d} => {verdict}; "
              f"[T4] unit-coeff winners {unit_wins}/{len(winners)} (coeff-interference persists if low)")

if __name__ == "__main__":
    plist = primes_1_mod_n(8, 16, 2)   # 17, 41
    run(8, plist, 2)
    run(8, plist, 3)
    print("\nDONE")
