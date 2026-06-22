#!/usr/bin/env python3
"""
#444 door-(iv)/C71 — (a) is the multi-term dominance + winning-support set STABLE at a STRUCTURED
Fermat-type prime (rule-2 stress), and (b) does the g0-ADJACENCY candidate hold there?

The winning multi-term supports at n=8,k=2 were prime-independent {(1,3,4),(2,3,6),(3,4)} across
p in {17,41,521}. CYCLE-5 observation: every winner TOUCHES the {deg(g0), deg(g0)+1} band
(g0 = X^{k+1}, deg=3 at k=2). This probe re-runs the EXACT support sweep at the FERMAT prime
p=257 = 2^8+1 (highly structured, the brief's rule-2 "structured Fermat-type" stress) to check both
the dominance gap and the winning-support / g0-adjacency stability against a structured prime.

EXACT full-alpha-sweep, EXACT max-agreement, thin mu_8 (NEVER n=q-1), k=2 Johnson thr=4/8, exhaustive
over all <=3-term supports, unit + non-unit coeffs.
"""
import itertools
from math import sqrt, ceil

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

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

def run(n, p, k):
    rho = k/n; thr = ceil(sqrt(rho)*n); dg = k+1
    w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
    g0 = evalf({dg: 1}, dom, p)
    print(f"\n=== n={n} k={k} thr={thr}/{n} p={p} (Fermat 2^8+1={'YES' if p==257 else 'no'}) "
          f"deg(g0)={dg} ===")
    s1 = max(bad_strength(evalf({b:1}, dom, p), dom, k, p, thr, g0) for b in range(1, n))
    s23 = 0; winners = []
    for s in (2, 3):
        for supp in itertools.combinations(range(1, n), s):
            for cp in ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1)):
                fv = evalf({supp[i]: cp[i] for i in range(s)}, dom, p)
                if all(x==0 for x in fv): continue
                st = bad_strength(fv, dom, k, p, thr, g0)
                if st > s23: s23 = st; winners = [(supp, tuple(cp))]
                elif st == s23 and st > 0: winners.append((supp, tuple(cp)))
    win_supp = sorted(set(s for s,_ in winners))
    unit_wins = sum(1 for _,c in winners if set(c) == {1})
    band = {dg, dg+1}
    touch = sum(1 for s in win_supp if band & set(s))
    gap = s23 - s1
    print(f"  s1max={s1} s23max={s23} gap={gap:+d} "
          f"({'STRICT multi-term' if gap>0 else 'tie'})")
    print(f"  winning supports: {win_supp}")
    print(f"  [g0-adjacency] winners touching band {sorted(band)}: {touch}/{len(win_supp)} "
          f"({'HOLDS' if touch==len(win_supp) else 'FAILS'})")
    print(f"  [T4] unit-coeff winners: {unit_wins}/{len(winners)}")

if __name__ == "__main__":
    run(8, 257, 2)   # Fermat prime stress
    print("\nDONE")
