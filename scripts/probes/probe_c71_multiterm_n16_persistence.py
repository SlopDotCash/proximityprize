#!/usr/bin/env python3
"""
#444 door-(iv) Lane-1 — does the C71 multi-term DOMINANCE gap (s23max > s1max) PERSIST at n=16?

Both the original C71 probe (5dd3a409e) and the follow-on coeff-interference probe (3591ed7c8) ran
ONLY at n=8. The whole C71 multi-term line ("worst <=3-sparse adversary is strictly multi-term, not a
monomial, escaping the orbit pin") hinges on s23max=9 > s1max=8 at n=8. If that gap is an n=8 artifact
the line weakens; if it PERSISTS (or widens) at n=16 the multi-term residual is the genuine frontier.

This probe checks the gap at n=16 cheaply: thin mu_16 (n=2^4), PROPER subgroup, k=2 so rho=2/16=0.125
(still a valid thin prize regime; Johnson agreement thr=ceil(sqrt(rho)*n)), EXACT C(16,2)=120-subset
max-agreement, EXACT full-alpha-sweep bad-strength, NEVER n=q-1, two structured primes spanning
p<=n^3 and p>n^3. Monomial directions exhaustively; 2-/3-term supports budgeted (sampled, unit + a
couple of non-unit coeff choices, since 3591ed7c8 showed non-unit ratios matter).
Reports s1max vs s23max and whether the dominance gap survives.
"""
import itertools, random
from math import sqrt, ceil

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

def run(n, plist, k, n_supports):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson-agreement thr={thr}/{n} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        assert len(set(dom)) == n
        g0 = evalf({k+1: 1}, dom, p)
        tag = "p>n^3" if p > n**3 else "p<=n^3"
        # 1-sparse: all monomials
        s1 = 0; s1arg = None
        for b in range(1, n):
            st = bad_strength(evalf({b:1}, dom, p), dom, k, p, thr, g0)
            if st > s1: s1 = st; s1arg = (b,)
        # 2/3-sparse: budgeted supports, unit + non-unit coeffs
        s23 = 0; s23arg = None
        random.seed(23)
        for s in (2, 3):
            sup_all = list(itertools.combinations(range(1, n), s))
            if len(sup_all) > n_supports: sup_all = random.sample(sup_all, n_supports)
            for supp in sup_all:
                for cp in ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1)):
                    cf = {supp[i]: cp[i] for i in range(s)}
                    fv = evalf(cf, dom, p)
                    if all(x==0 for x in fv): continue
                    st = bad_strength(fv, dom, k, p, thr, g0)
                    if st > s23: s23 = st; s23arg = (supp, tuple(cp))
        gap = s23 - s1
        verdict = ("DOMINANCE PERSISTS (multi-term worst, gap>0)" if gap > 0 else
                   "gap CLOSED at this n (monomial ties/wins)")
        print(f"  p={p} ({tag}): s1max={s1} {s1arg}  s23max={s23} {s23arg}  gap={gap:+d}  => {verdict}")

if __name__ == "__main__":
    # n=16, k=2 (thin rho=0.125), one small + one large prime, 40 sampled multi-term supports each sparsity
    run(16, primes_1_mod_n(16, 32, 1) + primes_1_mod_n(16, 16**3+1, 1), 2, 40)
    print("\nDONE")
