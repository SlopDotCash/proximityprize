#!/usr/bin/env python3
"""
#444 door-(iv) Lane-1 — FRESH object: the MULTI-TERM worst-case strata opened by C71SparseOrbitGap
(commit 5dd3a409e). That commit proved the worst <=3-sparse FRI adversary on thin mu_n is STRICTLY
multi-term (s23max=9 > s1max=8) so it ESCAPES the action-orbit eigenvector pin. The residual the
file leaves OPEN: "a non-orbit incidence bound on the 2- or 3-term strata."

The prior probe (probe_c71_sparse_orbit_gap.py) reported only the MAX strength value, never WHICH
support sets achieve it. The Lane-1 mandate ("is the worst-b set itself structured?") is settled for
the MONOMIAL worst-b set (DISPROOF_LOG: coset-closed but additively spread / multiplicatively
generic) — but that object is the single-frequency b. The MULTI-TERM direction-support set is a
DIFFERENT, NEWLY-OPENED object. This probe asks the non-redundant question:

  Among the <=3-sparse directions f that ACHIEVE the worst bad-set strength s23max, is the SET of
  winning support-exponent tuples {(i,j), (i,j,l)} arithmetically STRUCTURED (an exploitable handle
  for a non-orbit incidence bound), or generic?

Structure tests on the winning support set:
  (T1) dilation-coset structure: do winning supports lie in a single residue class mod the
       2-adic valuation pattern / mod small d? (the eigenvector pin keys on mu^i; mu has order n, so
       i mod n matters — but deg<n so i in 1..n-1, i mod n = i; instead test i-j gaps)
  (T2) GAP structure: is the multiset of pairwise exponent-gaps {i-j} of winning supports
       concentrated (few values) or spread over all of 1..n-1?
  (T3) self-similarity under doubling i->2i mod n (the 2-power dilation that the thin subgroup's
       Frobenius/squaring acts by): is the winning support set closed / orbit-structured under x2?
  (T4) coefficient dependence: does the worst strength depend on the coeff RATIO (genuine 2-term
       interference) or only on the support (would mean it's really a support-incidence object)?

EXACT full alpha-sweep, EXACT max-agreement, thin mu_n n=2^a, NEVER n=q-1, multi-prime incl p>n^3.
n=8 exhaustive over ALL <=3 supports (not sampled); n=16 with bounded support budget.
"""
import itertools, random
from math import gcd, sqrt, ceil
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
        if (p - 1) % n == 0 and is_prime(p):
            out.append(p)
        p += 2
    return out

def prime_factors(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            fs.add(d); m //= d
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
    n = len(dom); idx = list(range(n)); best = 0
    for S in itertools.combinations(idx, k):
        xs = [dom[i] for i in S]; ys = [v[i] for i in S]; agree = 0
        for jj in range(n):
            xq = dom[jj]; num = 0
            for a in range(k):
                term = ys[a]; xa = xs[a]
                for b in range(k):
                    if b == a: continue
                    term = term * ((xq - xs[b]) % p) % p * pow((xa - xs[b]) % p, p-2, p) % p
                num = (num + term) % p
            if num == v[jj]:
                agree += 1
        if agree > best:
            best = agree
            if best == n: break
    return best

def bad_strength(fvals, dom, k, p, thr, g0vals):
    n = len(dom); bad = 0
    for alpha in range(1, p):
        v = [(g0vals[j] + alpha*fvals[j]) % p for j in range(n)]
        if max_agreement_to_RS(v, dom, k, p) >= thr:
            bad += 1
    return bad

def evalf(coeffs, dom, p):
    return [sum(c*pow(x,pos,p) for pos,c in coeffs.items()) % p for x in dom]

def doubling_orbit(supp, n):
    """orbit of a support tuple under i -> 2i mod n (mod n; exponents in 1..n-1)."""
    seen = set()
    cur = tuple(sorted((2*i) % n for i in supp))
    s = tuple(sorted(supp))
    # walk the doubling map on the SET
    orb = {s}
    t = s
    for _ in range(n):
        t = tuple(sorted(((2*i) % n) for i in t))
        if t in orb: break
        orb.add(t)
    return orb

def run(n, plist, k, exhaustive):
    rho = k/n; thr = ceil(sqrt(rho)*n)
    print(f"\n=== n={n} k={k} rho={rho:.3f} Johnson-agreement thr={thr}/{n} exhaustive={exhaustive} ===")
    for p in plist:
        w = root_of_unity(p, n); dom = [pow(w,j,p) for j in range(n)]
        assert len(set(dom)) == n
        g0 = evalf({k+1: 1}, dom, p)
        tag = "p>n^3" if p > n**3 else "p<=n^3"
        # 1-sparse baseline
        s1 = 0
        for b in range(1, n):
            s1 = max(s1, bad_strength(evalf({b:1}, dom, k, p, ), dom, k, p, thr, g0)) if False else s1
        for b in range(1, n):
            s1 = max(s1, bad_strength(evalf({b:1}, dom, p), dom, k, p, thr, g0))
        # 2/3-sparse: track WHICH supports achieve the max, and whether coeff-ratio matters
        best = 0
        winners = []          # (support_tuple, coeff_tuple)
        support_best = {}     # support -> best strength over coeff choices (coeff-dependence test)
        coeff_set = lambda s: ([1]*s, [1]+[2]*(s-1), [1]+[p-1]*(s-1), [1]+[3]*(s-1))
        for s in (2, 3):
            sup_all = list(itertools.combinations(range(1, n), s))
            if not exhaustive and len(sup_all) > 60:
                random.seed(7); sup_all = random.sample(sup_all, 60)
            for supp in sup_all:
                loc_best = 0
                for cp in coeff_set(s):
                    cf = {supp[i]: cp[i] for i in range(s)}
                    fv = evalf(cf, dom, p)
                    if all(x==0 for x in fv): continue
                    st = bad_strength(fv, dom, k, p, thr, g0)
                    loc_best = max(loc_best, st)
                    if st > best:
                        best = st; winners = [(supp, tuple(cp))]
                    elif st == best and st > 0:
                        winners.append((supp, tuple(cp)))
                support_best[supp] = loc_best
        # analyze winning supports
        win_supports = sorted(set(s for s,_ in winners))
        print(f"  p={p} ({tag}): s1max={s1} s23max={best}  #winning(support,coeff)={len(winners)} "
              f"#distinct winning supports={len(win_supports)}")
        if not win_supports:
            continue
        # T2: gap multiset
        gaps = Counter()
        for supp in win_supports:
            for a,b in itertools.combinations(supp,2):
                gaps[abs(a-b)] += 1
        # gaps mod n and as differences mod n (dilation-relevant)
        gaps_modn = Counter()
        for supp in win_supports:
            for a,b in itertools.combinations(supp,2):
                gaps_modn[(a-b) % n] += 1
        # T3: doubling closure — is the winning support SET closed under i->2i mod n?
        winset = set(win_supports)
        closed = all(doubling_orbit(s,n) <= (winset | {tuple(sorted(s))}) for s in win_supports) \
                 if len(win_supports) < 200 else None
        # better: fraction of winners whose full doubling orbit is also winning
        orbit_closed_count = 0
        for s in win_supports:
            orb = doubling_orbit(s, n)
            if orb <= winset:
                orbit_closed_count += 1
        # T4: coeff dependence — among winning supports, did unit-coeff [1,1,..] alone achieve best?
        unit_wins = sum(1 for s,c in winners if set(c) == {1})
        print(f"     winning supports (first 12): {win_supports[:12]}")
        print(f"     [T2] pairwise gap multiset (|i-j|): {dict(sorted(gaps.items()))}")
        print(f"     [T2'] dilation gap mod n ((i-j)%n): {dict(sorted(gaps_modn.items()))}")
        print(f"     [T3] doubling(x2 mod n)-orbit-closed winning supports: {orbit_closed_count}/{len(win_supports)}")
        print(f"     [T4] winners achieved by UNIT coeffs [1,..,1]: {unit_wins}/{len(winners)} "
              f"(low => genuine coeff-interference object, not pure support-incidence)")

if __name__ == "__main__":
    # n=8 exhaustive over ALL <=3 supports; n=16 budgeted
    run(8, primes_1_mod_n(8, 16, 2) + primes_1_mod_n(8, 8**3+1, 1), 2, exhaustive=True)
    run(16, primes_1_mod_n(16, 32, 1) + primes_1_mod_n(16, 16**3+1, 1), 4, exhaustive=False)
    print("\nDONE")
