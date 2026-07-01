"""
probe_444_r4_overlap.py  (#444 -- pin the EXACT mechanism: type-overlap = additive coincidence)

Findings from typedecomp:
  - r=3: antipodal types are DISJOINT in gamma-space; per-type O_P sums cleanly.
    r=3 per-type O_P: n16 {(0,4):4,(1,2):2}, n32 {(0,4):24,(1,2):4}. 4+2=6, 24+4=28=C(q,2).
  - r=4 n=32: TYPES OVERLAP. 32 gammas shared across types. SUM per-type O_P=99 != total 97.

This probe pins WHY:
  1. r=3 per-type closed form: is (0,4)-type O_P and (1,2)-type O_P each clean in q=n/4?
     n16: (0,4)->4, (1,2)->2.  n32: (0,4)->24, (1,2)->4.
     Try: (0,4): 4=? , 24=? ; (1,2): 2=?, 4=?  -- ratios 6 and 2. Fit poly in q.
  2. r=4 OVERLAP: take the 32 shared gammas at n=32. For EACH, find ALL antipodal types of
     bad subsets producing it. Show explicitly that the SAME scalar gamma is realized by
     subsets of DIFFERENT antipodal type => a "char-0 additive coincidence" that breaks the
     clean type-by-type descent (cause (b)+(c) together).
  3. Quantify: total_OP = SUM(per-type OP) - (overlap correction). Is overlap correction itself
     clean? n=32: 99-97=2. So 2 orbits are double counted.
  4. DESCENT CHECK: for a (p,j)-type bad subset, the pair->zeta^2 descent maps it to p elements
     of mu_{n/2} + j signed singletons. Verify the descended object reproduces gamma, and check
     whether DIFFERENT original types descend to the SAME mu_{n/2} configuration (the overlap).

p = BabyBear 2013265921.
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict

p = 2013265921

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 1000):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError

def band_gamma_idx(Sidx, pe, pf, mu, k, a0):
    pts = [mu[i] for i in Sidx]
    m = len(pts)
    def interp(vals):
        A = [[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
        M = [A[i][:] + [vals[i] % p] for i in range(m)]
        for col in range(m):
            piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            inv = pow(M[col][col], p - 2, p)
            M[col] = [(v * inv) % p for v in M[col]]
            for rr in range(m):
                if rr != col and M[rr][col] % p != 0:
                    c = M[rr][col]
                    M[rr] = [(M[rr][t] - c * M[col][t]) % p for t in range(m + 1)]
        return [M[i][m] % p for i in range(m)]
    c0 = interp([pe[i] for i in Sidx])
    c1 = interp([pf[i] for i in Sidx])
    if c0 is None or c1 is None:
        return None
    gam = None; nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None
    return gam if nd else None

def antipodal_type(Sidx, n):
    h = n // 2
    Sset = set(Sidx)
    pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
    singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
    return (pairs, singles)

def gamma_to_types(n, r, e, f, mu):
    """Map each nonzero bad gamma -> Counter of antipodal types that produce it,
       and -> list of representative subsets per type."""
    k = r - 1; a0 = r + 1
    pe = [pow(x, e, p) for x in mu]
    pf = [pow(x, f, p) for x in mu]
    gt = defaultdict(Counter)
    grep = defaultdict(dict)  # gamma -> {type: Sidx}
    zero_subs = 0
    for Sidx in itertools.combinations(range(n), a0):
        gv = band_gamma_idx(Sidx, pe, pf, mu, k, a0)
        if gv is None:
            continue
        if gv % p == 0:
            zero_subs += 1
            continue
        t = antipodal_type(Sidx, n)
        gt[gv][t] += 1
        if t not in grep[gv]:
            grep[gv][t] = Sidx
    return gt, grep

def analyze(n, r, e, f, label):
    mu = [pow(w_of_order(n), i, p) for i in range(n)]
    gt, grep = gamma_to_types(n, r, e, f, mu)
    mult = pow(mu[1], (e - f) % n, p)
    print(f"\n### {label}: n={n} r={r} line (x^{e},x^{f}) ###")
    # how many gammas are multi-type
    multi = {g: ts for g, ts in gt.items() if len(ts) > 1}
    print(f"  total distinct nonzero gamma = {len(gt)}; multi-type gamma = {len(multi)}")
    # distribution of "number of types per gamma"
    ntypes_dist = Counter(len(ts) for ts in gt.values())
    print(f"  #types-per-gamma distribution: {dict(sorted(ntypes_dist.items()))}")
    # For multi-type gammas show a few + the descended structure
    if multi:
        sample = list(multi.items())[:3]
        for g, ts in sample:
            print(f"    gamma={g}: produced by types {dict(ts)}")
            for t, S in grep[g].items():
                exps = sorted(S)
                # descend: pairs -> 2*j mod n (square = w^{2j}), singles stay signed
                h = n // 2
                Sset = set(exps)
                pairs = [j for j in exps if j < h and (j + h) in Sset]
                singles = [j for j in exps if (j + h) % n not in Sset]
                descended = sorted((2 * j) % n for j in pairs)  # pair-squares in mu_{n/2} (as exps mod n, even)
                print(f"      type {t} S-exps={exps} pair-exps={pairs} singletons={singles} "
                      f"descended-pair-squares(exp mod n)={descended}")
    # Per-type orbit count and the overlap correction
    type_gammas = defaultdict(set)
    for g, ts in gt.items():
        for t in ts:
            type_gammas[t].add(g)
    def orbits(gset):
        rem = set(gset); o = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; orb = set()
            for _ in range(n):
                orb.add(cur); cur = cur * mult % p
            o += 1; rem -= orb
        return o
    sumOP = sum(orbits(gs) for gs in type_gammas.values())
    totOP = orbits(set(gt.keys()))
    print(f"  SUM per-type O_P = {sumOP} ; TOTAL O_P = {totOP} ; overlap correction = {sumOP-totOP}")
    return gt, type_gammas, mult

def fit_r3_per_type():
    print("="*90)
    print("r=3 per-type O_P closed form (the CLEAN baseline)")
    print("="*90)
    # data collected at n=16,32,64 for the r=3 maximizer (x^{n/2},x^{n/2-1})
    data = {}
    for n in [16, 32, 64]:
        mu = [pow(w_of_order(n), i, p) for i in range(n)]
        e, f = n // 2, n // 2 - 1
        gt, type_gammas, mult = analyze(n, 3, e, f, f"r=3 calib")
        data[n] = {t: gs for t, gs in type_gammas.items()}
    # per-type O_P across n
    print("\n  r=3 per-type O_P table (q=n/4 = 4,8,16):")
    alltypes = set()
    for n in data:
        alltypes |= set(data[n])
    def orbits_n(gset, n):
        mu = [pow(w_of_order(n), i, p) for i in range(n)]
        e, f = n // 2, n // 2 - 1
        mult = pow(mu[1], (e - f) % n, p)
        rem = set(gset); o = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; orb = set()
            for _ in range(n):
                orb.add(cur); cur = cur * mult % p
            o += 1; rem -= orb
        return o
    for t in sorted(alltypes):
        row = {}
        for n in [16, 32, 64]:
            row[n] = orbits_n(data[n].get(t, set()), n)
        print(f"    type {t}: O_P = {[row[n] for n in [16,32,64]]} (q=4,8,16)")
        # try clean fit
        q = [4, 8, 16]
        v = [row[16], row[32], row[64]]
        for name, fn in [("C(q,2)", lambda q: comb(q,2)),
                         ("C(q-1,2)", lambda q: comb(q-1,2)),
                         ("C(q,2)-q+1?", lambda q: comb(q,2)),
                         ("(q/2)*(q/2-1)", lambda q: (q//2)*(q//2-1)),
                         ("C(q,2)/?", lambda q: comb(q,2))]:
            if [fn(qq) for qq in q] == v:
                print(f"        MATCH {name}")

if __name__ == "__main__":
    fit_r3_per_type()
    print("\n" + "="*90)
    print("r=4 OVERLAP mechanism (n=16 disjoint vs n=32 overlapping)")
    print("="*90)
    for n in [16, 32]:
        analyze(n, 4, n // 2 + 2, n // 4 + 1, "r=4 maximizer")
