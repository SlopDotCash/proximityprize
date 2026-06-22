#!/usr/bin/env python3
"""
#444 door-(iv) Lane-1 — CONFIRM the C71 g0-adjacency band rule + strict multi-term dominance at n=16.

The prior C71 worker (7 cycles, commits 3591ed7c8..d7b4bc457) established at n=8:
  - strict multi-term dominance s23max > s1max (gap=+1) at k=2 (k=2-specific, ties at k=3),
  - the worst multi-term winning support ALWAYS contains deg(g0)=k+1 (100% of winners vs 38% baseline),
  - prime-independent incl. Fermat prime 2^8+1, coeff-interference (non-unit ratios win).
It EXPLICITLY LEFT OPEN, flagged for a "compute-heavier worker":
  "confirm the band rule + dominance at n=16+ (n=16 EXACT max-agreement too slow in pure Python)".

This probe closes that gap with a NUMPY-VECTORIZED exact max-agreement (the alpha-sweep and the
inner agreement counts vectorize cleanly over F_p), so n=16 EXACT is tractable. Same EXACT setup as
probe_c71_multiterm_support_structure.py: thin mu_n (n=2^a, PROPER subgroup), g0 = X^{k+1} (the
non-codeword), bad-strength = #{alpha in 1..p-1 : maxAgree(g0 + alpha*f, RS_k) >= Johnson thr},
NEVER n=q-1, multiple structured primes spanning p<=n^3 and p>n^3 incl. a Fermat-type prime.

We report, at n=16, k in {2,3}:
  s1max  (monomial worst), s23max (<=3-term worst), the GAP,
  the WINNING multi-term support set, and the g0-adjacency stats:
    - fraction of ALL <=3-supports that contain deg(g0)=k+1   (baseline)
    - fraction of WINNING supports that contain deg(g0)=k+1   (the selectivity test)
    - fraction touching the band {deg(g0), deg(g0)+1}.
EXACT monomials (all). Multi-term: EXACT all <=3-supports for k=2; budgeted for k=3 (still large but
we cover all 2-term + sampled 3-term to keep it finite). Unit + non-unit coeff ratios (the [T4]
coeff-interference axis) included.
"""
import itertools, random
from math import sqrt, ceil
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
    """Precompute, for every k-subset S and every eval point j, the Lagrange-interp coefficients
    L[S][a][j] s.t. interp value at x_j = sum_a v[S[a]] * L[S][a][j].  Vectorized agreement later."""
    n = len(dom)
    subsets = list(itertools.combinations(range(n), k))
    domA = np.array(dom, dtype=np.int64)
    # L tensor: (numS, k, n)
    L = np.zeros((len(subsets), k, n), dtype=np.int64)
    for si, S in enumerate(subsets):
        xs = [dom[i] for i in S]
        for a in range(k):
            xa = xs[a]
            # basis poll_a(x_j) = prod_{b!=a} (x_j - x_b)/(x_a - x_b)
            num = np.ones(n, dtype=np.int64)
            den = 1
            for b in range(k):
                if b == a: continue
                num = (num * ((domA - xs[b]) % p)) % p
                den = (den * ((xa - xs[b]) % p)) % p
            deninv = pow(int(den), p-2, p)
            L[si, a, :] = (num * deninv) % p
    return subsets, L

def max_agreement_matrix(V, subsets, L, p):
    """V: (A, n) array of A vectors (the alpha-sweep). Returns max agreement to RS_k per row.
    For each subset S: interp = sum_a V[:,S[a]] * L[si,a,:]  -> (A,n); agree where == V.
    Max over subsets."""
    A, n = V.shape
    best = np.zeros(A, dtype=np.int64)
    for si in range(L.shape[0]):
        S = subsets[si]
        # interp[r, j] = sum_a V[r, S[a]] * L[si, a, j]
        # V[:, S] -> (A, k); L[si] -> (k, n)
        interp = (V[:, S] @ L[si]) % p   # (A, n)
        agree = (interp == V).sum(axis=1)
        np.maximum(best, agree, out=best)
    return best

def bad_strength_vec(fvals, g0, subsets, L, p, thr):
    """#{alpha in 1..p-1 : maxAgree(g0 + alpha*fvals) >= thr}, fully vectorized over alpha."""
    n = len(fvals)
    alphas = np.arange(1, p, dtype=np.int64)           # (p-1,)
    f = np.array(fvals, dtype=np.int64)
    g = np.array(g0, dtype=np.int64)
    V = (g[None, :] + alphas[:, None] * f[None, :]) % p  # (p-1, n)
    ma = max_agreement_matrix(V, subsets, L, p)
    return int((ma >= thr).sum())

def evalf(coeffs, dom, p):
    return [sum(c*pow(x,e,p) for e,c in coeffs.items()) % p for x in dom]

def run(n, plist, k, three_term_budget):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson-agreement thr={thr}/{n} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        assert len(set(dom)) == n
        subsets, L = build_lagrange_tensors(dom, k, p)
        g0deg = k+1
        g0 = evalf({g0deg: 1}, dom, p)
        tag = "p>n^3" if p > n**3 else "p<=n^3"

        # 1-sparse: all monomials X^b, b in 1..n-1
        s1 = 0; s1arg = None
        for b in range(1, n):
            st = bad_strength_vec(evalf({b:1}, dom, p), g0, subsets, L, p, thr)
            if st > s1: s1 = st; s1arg = (b,)

        # multi-term: 2-term EXACT (all), 3-term budgeted. coeff ratios: unit, [1,2..], [1,p-1..]
        s23 = 0; s23arg = None
        winners = []   # list of (support_tuple, coeff_tuple, strength) achieving s23max (refilled)
        def consider(supp, cp):
            nonlocal s23, s23arg, winners
            cf = {supp[i]: cp[i] for i in range(len(supp))}
            fv = evalf(cf, dom, p)
            if all(x==0 for x in fv): return
            st = bad_strength_vec(fv, g0, subsets, L, p, thr)
            if st > s23:
                s23 = st; s23arg = (supp, tuple(cp)); winners = [(supp, tuple(cp), st)]
            elif st == s23 and st > 0:
                winners.append((supp, tuple(cp), st))

        coeff_choices = lambda s: ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1), [1]+[3]*(s-1))
        # 2-term: exhaustive
        for supp in itertools.combinations(range(1, n), 2):
            for cp in coeff_choices(2): consider(supp, cp)
        # 3-term: budgeted sample (exhaustive C(15,3)=455 is fine actually -> do all)
        three = list(itertools.combinations(range(1, n), 3))
        if len(three) > three_term_budget:
            random.seed(71); three = random.sample(three, three_term_budget)
        for supp in three:
            for cp in coeff_choices(3): consider(supp, cp)

        gap = s23 - s1
        # g0-adjacency stats on the WINNING support set (dedup supports)
        win_supps = sorted({w[0] for w in winners})
        all_supps = list(itertools.combinations(range(1, n), 2)) + three
        base_contain = sum(1 for s in all_supps if g0deg in s) / len(all_supps)
        win_contain  = (sum(1 for s in win_supps if g0deg in s) / len(win_supps)) if win_supps else 0.0
        band = {g0deg, g0deg+1}
        win_band = (sum(1 for s in win_supps if band & set(s)) / len(win_supps)) if win_supps else 0.0
        verdict = "DOMINANCE PERSISTS" if gap > 0 else "gap CLOSED (monomial ties/wins)"
        print(f"  p={p} ({tag}): s1max={s1}{s1arg}  s23max={s23}  gap={gap:+d}  [{verdict}]")
        print(f"      winning supports ({len(win_supps)}): {win_supps[:12]}{' ...' if len(win_supps)>12 else ''}")
        print(f"      g0-adjacency: deg(g0)={g0deg}  baseline contain={base_contain:.2f}  "
              f"WINNERS contain deg(g0)={win_contain:.2f}  touch band {sorted(band)}={win_band:.2f}")

if __name__ == "__main__":
    import time
    t0 = time.time()
    # n=16: small prime (p<=n^3=4096) and large prime (p>n^3); Fermat 2^8+1=257 is <n^3 here, add a
    # large 1-mod-16 prime > 4096 for the p>n^3 stress.
    P_small = primes_1_mod_n(16, 17, 2)        # smallest 1-mod-16 primes
    P_large = primes_1_mod_n(16, 16**3+1, 1)   # first 1-mod-16 prime > n^3
    plist = P_small + P_large
    print("n=16 primes:", plist, " (n^3 =", 16**3, ")")
    run(16, plist, 2, three_term_budget=455)   # k=2: 2-term exhaustive, 3-term exhaustive (455)
    print(f"\n[k=2 done @ {time.time()-t0:.1f}s]")
    run(16, plist, 3, three_term_budget=455)   # k=3
    print(f"\nDONE @ {time.time()-t0:.1f}s")
