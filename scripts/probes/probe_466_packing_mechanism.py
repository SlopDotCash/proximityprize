#!/usr/bin/env python3
"""
#466 LANE FS2 -- the PACKING/DENSITY mechanism for floor-bad(n) = {p_min(n)}.

GOAL (task (a)): find a statistic S(n,p) of mu_n <= F_p^x (the n-th roots of unity)
that is > threshold exactly at p = p_min(n) (the least prime == 1 mod n, the ONLY
floor-bad prime at n=16,32) and < threshold for every larger p == 1 mod n --
i.e. make "only the smallest/tightest prime packs mu_n densely enough to force
the forbidden adjacent-7th-type profile" QUANTITATIVE.

Mechanism recap (exact, from probe_466_successor_norm.py / _FloorSuccessorNorm.lean):
  points x_j = g0^j  (g0 = primitive n-th root of unity mod p, p == 1 mod n);
  a structured "adjacent-7th-type" pattern A (subset of Z/n, 5n/8 points, four
  residue-mod-4 classes: two minority classes take agr_min = 3m/4 of m positions,
  two majority take agr_maj = m/2, m = n/4) is REALIZABLE at p iff
    V_A(t) = prod_{j in A}(t - x_j)   (monic, deg |A|),
    R(t)   = t^{3n/4} mod V_A(t),
  has deg R <= n/2, i.e. the obstruction coeffs r_k (k in [n/2+1, |A|-1]) vanish.
  DEFECT(A,p) = #{k in [n/2+1,|A|-1] : r_k != 0}.  Realizable <=> defect 0.
  floor-bad(p) <=> min_A DEFECT(A,p) = 0.

This probe, per prime p == 1 mod n:
  (1) min_A DEFECT over ALL structured patterns (exhaustive at n=16; annealed at 32/64);
  (2) a battery of PACKING statistics of the point set mu_n in F_p, to see which
      (if any) is monotone in p and crosses a fixed threshold exactly at p_min.

Statistics computed (mu_n as integer reps in [0,p)):
  density     = n/p
  minGapNorm  = (min circular gap between adjacent mu_n reps) * n / p   in (0,1]
  maxGapNorm  = (max circular gap) * n / p                              in [1, n)
  minPairAbs  = min circular |x_i - x_j| over pairs (== min raw gap)
  clusterDiam = smallest interval (circular) containing >= ceil(n/4)+1 mu_n reps,
                normalized by p/n (a covering/crowding statistic for the tightest class)
  allResidues = 1 iff mu_n == F_p^x (n == p-1)   [the n=16 degeneracy flag]
"""
import sys
from itertools import combinations

# ----------------------------------------------------------------------------
def isprime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def generator(p):
    m = p-1; fac = []; mm = m; d = 2
    while d*d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fac.append(mm)
    for h in range(2, p):
        if all(pow(h, (p-1)//q, p) != 1 for q in fac):
            return h
    raise RuntimeError("no generator")

def mu_reps(p, n):
    g = generator(p); g0 = pow(g, (p-1)//n, p)
    return [pow(g0, j, p) for j in range(n)], g0

def least_prime_1modn(n):
    p = n+1
    while True:
        if isprime(p): return p
        p += n

def primes_1modn(n, count, start=None):
    out = []
    p = (start if start else n) + 1
    # ensure p == 1 mod n
    if p % n != 1:
        p += (1 - p) % n
    while len(out) < count:
        if p % n == 1 and isprime(p):
            out.append(p)
        p += n
    return out

# ----------------------------------------------------------------------------
# realizability defect over F_p
# ----------------------------------------------------------------------------
def defect_modp(A, Xpow, p, half, deg34):
    V = [1]
    for j in A:
        root = Xpow[j]; newV = [0]*(len(V)+1)
        for i, c in enumerate(V):
            newV[i] = (newV[i] - root*c) % p
            newV[i+1] = (newV[i+1] + c) % p
        V = newV
    D = len(V)-1
    r = [(-V[k]) % p for k in range(D)]
    for _ in range(deg34 - D):
        top = r[D-1]; nr = [0]*D
        for k in range(D-1, 0, -1):
            nr[k] = (r[k-1] - top*V[k]) % p
        nr[0] = (-top*V[0]) % p
        r = nr
    return sum(1 for k in range(half+1, D) if r[k] != 0)

def min_defect_exhaustive(p, n, Xpow):
    m = n//4; half = n//2; deg34 = 3*n//4
    agr_min = m - m//4; agr_maj = m - m//2
    cls = [[j for j in range(n) if j % 4 == c] for c in range(4)]
    cmin = list(combinations(range(m), agr_min))
    cmaj = list(combinations(range(m), agr_maj))
    best = 10**9; nreal = 0
    for c0 in range(4):
        mn0, mn1, mj0, mj1 = c0, (c0+1)%4, (c0+2)%4, (c0+3)%4
        for a in cmin:
            for b in cmin:
                for d in cmaj:
                    for e in cmaj:
                        A = sorted([cls[mn0][i] for i in a] + [cls[mn1][i] for i in b] +
                                   [cls[mj0][i] for i in d] + [cls[mj1][i] for i in e])
                        dd = defect_modp(A, Xpow, p, half, deg34)
                        if dd < best: best = dd
                        if dd == 0: nreal += 1
    return best, nreal

def min_defect_anneal(p, n, Xpow, restarts=60, seed=1, stagn_cap=1500):
    import random
    m = n//4; half = n//2; deg34 = 3*n//4
    agr_min = m - m//4; agr_maj = m - m//2
    cls = [[j for j in range(n) if j % 4 == c] for c in range(4)]
    rng = random.Random(seed)
    best = 10**9
    for R in range(restarts):
        c0 = rng.randrange(4)
        classes = [c0, (c0+1)%4, (c0+2)%4, (c0+3)%4]
        agr = [agr_min, agr_min, agr_maj, agr_maj]
        sel = [rng.sample(range(m), agr[i]) for i in range(4)]
        def build(sel):
            A = []
            for ci, c in enumerate(classes):
                for i in sel[ci]: A.append(cls[c][i])
            return sorted(A)
        E = defect_modp(build(sel), Xpow, p, half, deg34); stagn = 0
        while stagn < stagn_cap and E > 0:
            ci = rng.randrange(4); cur = sel[ci]
            miss = [x for x in range(m) if x not in cur]
            if not miss: stagn += 1; continue
            pos = rng.randrange(len(cur)); c2 = cur[:]; c2[pos] = rng.choice(miss)
            s2 = sel[:]; s2[ci] = c2; E2 = defect_modp(build(s2), Xpow, p, half, deg34)
            if E2 <= E:
                if E2 < E: stagn = 0
                else: stagn += 1
                sel = s2; E = E2
            else: stagn += 1
        if E < best: best = E
        if best == 0: break
    return best

# ----------------------------------------------------------------------------
# packing statistics of mu_n <= F_p
# ----------------------------------------------------------------------------
def packing_stats(reps, p, n):
    s = sorted(reps)
    gaps = [s[i+1]-s[i] for i in range(len(s)-1)] + [s[0] + p - s[-1]]
    mn = min(gaps); mx = max(gaps)
    density = n / p
    minGapNorm = mn * n / p
    maxGapNorm = mx * n / p
    # clusterDiam: tightest window (circular) holding >= q elements, q = ceil(n/4)+1
    q = n//4 + 1
    ss = s + [x + p for x in s]  # double for circular windows
    best = p
    for i in range(len(s)):
        w = ss[i+q-1] - ss[i]
        if w < best: best = w
    clusterDiamNorm = best * n / p / (q-1)  # normalized: avg-gap units per element
    allResidues = 1 if n == p-1 else 0
    return dict(density=density, minGapNorm=minGapNorm, maxGapNorm=maxGapNorm,
                minPairAbs=mn, clusterDiamNorm=clusterDiamNorm, allResidues=allResidues)

# ----------------------------------------------------------------------------
def run(n, primes, exhaustive):
    print(f"\n########## n={n}  (p_min = {least_prime_1modn(n)}) ##########")
    hdr = f"{'p':>8} {'real?':>6} {'minDef':>7} {'nReal':>7} | {'density':>8} {'minGapN':>8} {'maxGapN':>8} {'minPair':>8} {'clDiamN':>8} {'allRes':>6}"
    print(hdr); print("-"*len(hdr))
    rows = []
    for p in primes:
        reps, g0 = mu_reps(p, n)
        st = packing_stats(reps, p, n)
        if exhaustive:
            md, nr = min_defect_exhaustive(p, n, reps)
        else:
            md = min_defect_anneal(p, n, reps); nr = -1
        real = "YES" if md == 0 else "no"
        rows.append((p, md, st))
        print(f"{p:>8} {real:>6} {md:>7} {nr:>7} | {st['density']:>8.4f} {st['minGapNorm']:>8.4f} "
              f"{st['maxGapNorm']:>8.3f} {st['minPairAbs']:>8} {st['clusterDiamNorm']:>8.4f} {st['allResidues']:>6}")
    # threshold analysis for each statistic
    print("\n  --- threshold analysis (is there tau separating p_min from the rest?) ---")
    bad = [r for r in rows if r[1] == 0]
    good = [r for r in rows if r[1] != 0]
    if not bad:
        print("  (no floor-bad prime found in this range)")
        return rows
    for key in ['density', 'minGapNorm', 'maxGapNorm', 'minPairAbs', 'clusterDiamNorm']:
        bvals = [r[2][key] for r in bad]
        gvals = [r[2][key] for r in good]
        # a statistic S "works high" if min(bad) > max(good); "works low" if max(bad) < min(good)
        hi_ok = (min(bvals) > max(gvals)) if gvals else True
        lo_ok = (max(bvals) < min(gvals)) if gvals else True
        # monotone-in-p check on the good primes
        gseq = [(r[0], r[2][key]) for r in good]
        mono_dec = all(gseq[i][1] >= gseq[i+1][1] for i in range(len(gseq)-1))
        mono_inc = all(gseq[i][1] <= gseq[i+1][1] for i in range(len(gseq)-1))
        verdict = []
        if hi_ok: verdict.append(f"SEPARATES-HIGH (bad>={min(bvals):.4f} > good<={max(gvals):.4f})")
        if lo_ok: verdict.append(f"SEPARATES-LOW (bad<={max(bvals):.4f} < good>={min(gvals):.4f})")
        if not verdict: verdict.append("does NOT separate")
        mono = "mono-dec" if mono_dec else ("mono-inc" if mono_inc else "NON-monotone")
        print(f"    {key:>15}: {'; '.join(verdict)}   [good-seq {mono}]")
    return rows

# ----------------------------------------------------------------------------
# FAST reliable mode: packing stats vs the KNOWN floor-bad = {p_min} (no defect search).
# floor-bad(16)={17}, floor-bad(32)={97} are EXACT (validated scanners); n=64 conj {193}.
# ----------------------------------------------------------------------------
def run_stats_only(n, count):
    pmin = least_prime_1modn(n)
    tag = "exact" if n in (16, 32) else "CONJECTURAL"
    print(f"\n### n={n}  floor-bad = {{{pmin}}} ({tag}) -- packing stats only ###")
    ps = primes_1modn(n, count)
    print(f"{'p':>8} {'bad?':>5} | {'density':>8} {'minGapN':>8} {'maxGapN':>8} {'minPair':>8} {'clDiamN':>8} {'allRes':>6}")
    rows = []
    for i, p in enumerate(ps):
        reps, _ = mu_reps(p, n)
        st = packing_stats(reps, p, n); bad = (i == 0)
        rows.append((p, bad, st))
        print(f"{p:>8} {('BAD' if bad else 'good'):>5} | {st['density']:>8.4f} {st['minGapNorm']:>8.4f} "
              f"{st['maxGapNorm']:>8.3f} {st['minPairAbs']:>8} {st['clusterDiamNorm']:>8.4f} {st['allResidues']:>6}")
    for key in ['density', 'minGapNorm', 'maxGapNorm', 'minPairAbs', 'clusterDiamNorm']:
        bv = [r[2][key] for r in rows if r[1]]; gv = [r[2][key] for r in rows if not r[1]]
        hi = min(bv) > max(gv); lo = max(bv) < min(gv)
        v = "SEP-HIGH" if hi else ("SEP-LOW" if lo else "NO-SEP ")
        print(f"    {key:>15}: {v}  bad={bv[0]:.4f}  good in [{min(gv):.4f},{max(gv):.4f}]")

def run_uniform_threshold_test():
    print("\n### UNIFORM-THRESHOLD FEASIBILITY: does a fixed tau separate p_min from p_2 across n? ###")
    print(f"{'n':>7} {'p_min':>9} {'p_2':>9} | {'n/p_min':>8} {'n/p_2':>8}")
    rows = []
    for k in range(2, 16):
        n = 2**k; ps = primes_1modn(n, 2)
        rows.append((n, ps[0], ps[1], n/ps[0], n/ps[1]))
        print(f"{n:>7} {ps[0]:>9} {ps[1]:>9} | {n/ps[0]:>8.4f} {n/ps[1]:>8.4f}")
    maxp2 = max(r[4] for r in rows); minp1 = min(r[3] for r in rows)
    am = max(rows, key=lambda r: r[4]); im = min(rows, key=lambda r: r[3])
    print(f"\n  A fixed tau must satisfy  tau <= n/p_min (all n)  AND  tau > n/p_2 (all n).")
    print(f"  min_n (n/p_min) = {minp1:.4f}   at n={im[0]} (p_min={im[1]})")
    print(f"  max_n (n/p_2)   = {maxp2:.4f}   at n={am[0]} (p_2={am[2]})")
    print(f"  UNIFORM tau exists?  need {maxp2:.4f} < {minp1:.4f}  ->  {maxp2 < minp1}")
    print(f"  COUNTERMODEL: n/p_2({am[0]}) = {am[0]}/{am[2]} = {am[4]:.4f}  >  "
          f"n/p_min({im[0]}) = {im[0]}/{im[1]} = {im[3]:.4f}")
    print(f"    i.e. {am[0]}*{im[1]} = {am[0]*im[1]}  >  {im[0]}*{am[2]} = {im[0]*am[2]}")
    print(f"    => a NON-least prime ({am[2]}, at n={am[0]}) is DENSER than a LEAST prime "
          f"({im[1]}=p_min({im[0]})).")

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "stats"
    if what in ("16", "all"):
        ps = primes_1modn(16, 60)  # 17, 97, 113, ...
        run(16, ps, exhaustive=True)
    if what in ("32anneal", "all"):
        ps = primes_1modn(32, 25)
        run(32, ps, exhaustive=False)
    if what in ("stats", "all"):
        run_stats_only(16, 14)
        run_stats_only(32, 14)
        run_stats_only(64, 12)
        run_uniform_threshold_test()
