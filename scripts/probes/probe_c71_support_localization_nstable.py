#!/usr/bin/env python3
"""
#444 door-(iv)/C71 Lane-1 — is ANY support-localization rule n-STABLE for the worst k=2 multi-term
adversary? (follow-up to the n=16 refutation b1fe21bc3)

Context: the prior worker proposed "worst-support ∋ deg(g0)=k+1" (n=8,k=2: 100%). My n=16,k=2 probe
REFUTED that (winners localize at n-1=15, only 0.33 contain deg(g0)). But n-1 is ALSO not universal:
the n=8 winners {(1,3,4),(2,3,6),(3,4)} contain NO 7=n-1. So neither deg(g0) NOR n-1 is n-stable.

This probe settles it: characterize the worst k=2 multi-term winning supports across n∈{8,16,32} and
test EVERY plausible fixed localization hypothesis on the winning-support set, prime-independently:
  H1: contains deg(g0)=k+1
  H2: contains n-1 (the inverse character X^{-1} on μ_n)
  H3: contains n/2 (the order-2 / quadratic character exponent)
  H4: contains a fixed exponent independent of n (none expected)
  H5: all winning exponents lie in a SMALL residue class mod small d (additive structure)
For each n we report s1max, s23max, gap, the winning support set, and the H1..H3 hit-fractions.
If no Hi holds uniformly across n∈{8,16,32}, the conclusion is: NO fixed-degree support-localization
lever survives — the support-side direction is dead, and any incidence bound must be intrinsic
(scale-relative), not keyed on a named exponent.

EXACT max-agreement via numpy vectorization over the alpha-sweep (same engine validated in
probe_c71_n16_g0adjacency_numpy.py, which reproduces the published n=8 numbers bit-for-bit). Thin μ_n
(n=2^a, PROPER subgroup), g0=X^{k+1}, NEVER n=q-1, multiple structured 1-mod-n primes.
n=32 is heavier (C(32,2)=496 subsets); 2-term exhaustive, 3-term sampled to stay in budget.
"""
import itertools, random
from math import sqrt, ceil, gcd
import numpy as np

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

def build_lagrange_tensors(dom, k, p):
    n = len(dom)
    subsets = list(itertools.combinations(range(n), k))
    domA = np.array(dom, dtype=np.int64)
    L = np.zeros((len(subsets), k, n), dtype=np.int64)
    for si, S in enumerate(subsets):
        xs = [dom[i] for i in S]
        for a in range(k):
            xa = xs[a]; num = np.ones(n, dtype=np.int64); den = 1
            for b in range(k):
                if b == a: continue
                num = (num * ((domA - xs[b]) % p)) % p
                den = (den * ((xa - xs[b]) % p)) % p
            deninv = pow(int(den), p-2, p)
            L[si, a, :] = (num * deninv) % p
    return subsets, L

def max_agreement_matrix(V, subsets, L, p):
    A, n = V.shape; best = np.zeros(A, dtype=np.int64)
    for si in range(L.shape[0]):
        S = subsets[si]
        interp = (V[:, S] @ L[si]) % p
        agree = (interp == V).sum(axis=1)
        np.maximum(best, agree, out=best)
    return best

def bad_strength_vec(fvals, g0, subsets, L, p, thr):
    alphas = np.arange(1, p, dtype=np.int64)
    f = np.array(fvals, dtype=np.int64); g = np.array(g0, dtype=np.int64)
    V = (g[None, :] + alphas[:, None] * f[None, :]) % p
    ma = max_agreement_matrix(V, subsets, L, p)
    return int((ma >= thr).sum())

def evalf(coeffs, dom, p):
    return [sum(c*pow(x,e,p) for e,c in coeffs.items()) % p for x in dom]

def run(n, plist, k, three_budget):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson thr={thr}/{n} ===")
    g0deg = k+1
    win_by_prime = []
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        assert len(set(dom)) == n
        subsets, L = build_lagrange_tensors(dom, k, p)
        g0 = evalf({g0deg: 1}, dom, p)
        s1 = 0
        for b in range(1, n):
            s1 = max(s1, bad_strength_vec(evalf({b:1}, dom, p), g0, subsets, L, p, thr))
        s23 = 0; winners = []
        def consider(supp, cp):
            nonlocal s23, winners
            cf = {supp[i]: cp[i] for i in range(len(supp))}
            fv = evalf(cf, dom, p)
            if all(x==0 for x in fv): return
            st = bad_strength_vec(fv, g0, subsets, L, p, thr)
            if st > s23: s23 = st; winners = [supp]
            elif st == s23 and st > 0: winners.append(supp)
        cc = lambda s: ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1), [1]+[3]*(s-1))
        for supp in itertools.combinations(range(1, n), 2):
            for cp in cc(2): consider(supp, cp)
        three = list(itertools.combinations(range(1, n), 3))
        if len(three) > three_budget:
            random.seed(71); three = random.sample(three, three_budget)
        for supp in three:
            for cp in cc(3): consider(supp, cp)
        wsupps = sorted(set(winners))
        win_by_prime.append((p, s1, s23, wsupps))
        # localization hypotheses on winning supports
        exps = set().union(*[set(s) for s in wsupps]) if wsupps else set()
        H1 = sum(1 for s in wsupps if g0deg in s)/len(wsupps) if wsupps else 0
        H2 = sum(1 for s in wsupps if (n-1) in s)/len(wsupps) if wsupps else 0
        H3 = sum(1 for s in wsupps if (n//2) in s)/len(wsupps) if wsupps else 0
        tag = "p>n^3" if p > n**3 else "p<=n^3"
        print(f"  p={p}({tag}): s1={s1} s23={s23} gap={s23-s1:+d}  winners={wsupps}")
        print(f"      H1(∋deg g0={g0deg})={H1:.2f}  H2(∋ n-1={n-1})={H2:.2f}  H3(∋ n/2={n//2})={H3:.2f}  win_exps={sorted(exps)}")
    # cross-prime stability
    sets = [tuple(w[3]) for w in win_by_prime]
    print(f"  cross-prime winning-set STABLE: {len(set(sets))==1}")
    return win_by_prime

if __name__ == "__main__":
    import time; t0=time.time()
    P8  = primes_1_mod_n(8, 17, 3)        # 17,41,73...
    P16 = primes_1_mod_n(16, 90, 3)       # 97,113,193
    P32 = primes_1_mod_n(32, 90, 2)       # 1-mod-32 primes
    r8  = run(8,  P8,  2, three_budget=455); print(f"[n=8 @ {time.time()-t0:.1f}s]")
    r16 = run(16, P16, 2, three_budget=455); print(f"[n=16 @ {time.time()-t0:.1f}s]")
    r32 = run(32, P32, 2, three_budget=300); print(f"[n=32 @ {time.time()-t0:.1f}s]")
    print("\n=== CROSS-n localization verdict (k=2) ===")
    for nm,r in [("n=8",r8),("n=16",r16),("n=32",r32)]:
        ws = r[0][3]; gdeg=3; nn=int(nm.split('=')[1])
        print(f"  {nm}: winners={ws}  ∋deg(g0)=3:{all(3 in s for s in ws)}  ∋(n-1)={nn-1}:{all((nn-1) in s for s in ws)}")
    print(f"\nDONE @ {time.time()-t0:.1f}s")
