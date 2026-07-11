#!/usr/bin/env python3
"""Probe: the P1 rate-quarter two-cover window (three_heavy_twoCover_window).

Question: can three distinct near-threshold-aligned pencil pairs through one base
codeword have aligned regions two-covering >= 3(T-1) - N = 704643071 coordinates
inside N = 2^30 while every pairwise aligned-region overlap is < k = 2^28?

Part A (combinatorics, exact integers): is the covering-overlap window satisfiable
as a bare set system in [N]?  Exact inclusion-exclusion + an explicit interval
construction.

Part B (RS algebra, scaled): with shared base b and stack u0 = b, aligned regions
are agreement sets A_i = {x : g_i(x) = u1(x)} of three distinct codewords g_i with
u1.  Realizing the window at shape (n, k=n/4, T-1 = floor(53n/96)) reduces to:
find f = g1-g2, g = g2-g3 of degree <= k-1 maximizing the balanced coincidence
mass W = r12 + r23 + r13 - t (r_ij = #roots of the difference in mu_n, t = triple
roots), with per-A_i balance |A_i| >= T-1 achievable iff
  r_ij + r_il + t + (share of singles) >= T-1 for each i and total mass suffices.
We search exhaustively at n=16 (F_17), and structured/randomized at n=32 (F_97),
n=64 (F_193), n=256 (F_257).

All arithmetic exact (Python ints / numpy int64 mod p).
"""

import itertools
import random
from math import comb

import numpy as np

# ---------------------------------------------------------------- Part A


def part_a():
    N = 2**30
    k = 2**28
    T = 592794966
    Tm1 = T - 1
    assert Tm1 == (53 * N) // 96
    demand = 3 * Tm1 - N
    cap = 3 * (k - 1)
    print("== Part A: pure combinatorial window ==")
    print(f"N={N} k={k} T-1={Tm1} two-cover demand={demand} overlap cap={cap}")
    assert demand == 704643071 and cap == 805306365
    # per-pair overlap must be >= 2(T-1)-N and < k; sum of pairwise >= demand.
    lo_pair = 2 * Tm1 - N
    print(f"per-pair forced overlap >= {lo_pair}, allowed < {k}")
    # explicit construction: equal pairwise overlap o, triple overlap t=0.
    # need 3o >= demand and o <= k-1 and union = 3(T-1) - 3o <= N.
    o = (demand + 2) // 3  # ceil(demand/3)
    assert 3 * o >= demand and o <= k - 1 and lo_pair <= o
    union = 3 * Tm1 - 3 * o
    assert union <= N
    # intervals inside [0,N): A = [0, Tm1); B = [Tm1-o, 2Tm1-o); C shares o with
    # each of A and B: place C = [0,o) u [2Tm1-2o, 2Tm1-2o + o) u fresh rest.
    A = (0, Tm1)
    B = (Tm1 - o, 2 * Tm1 - o)
    c_rest = Tm1 - 2 * o
    fresh_start = 2 * Tm1 - o
    assert fresh_start + c_rest <= N, (fresh_start + c_rest, N)
    # C = [0,o) (inside A only, since B starts at Tm1-o > o) u
    #     [B_end - o, B_end) (inside B only) u [fresh_start, fresh_start+c_rest)
    assert o < Tm1 - o  # the two C-chunks are disjoint and land in A-only/B-only
    AB = o  # |A n B| = o by construction: [Tm1-o, Tm1)
    AC = o
    BC = o
    twocover = AB + AC + BC  # t = 0
    print(f"explicit intervals: |AnB|=|AnC|=|BnC|={o}, two-cover={twocover}")
    assert twocover >= demand and max(AB, AC, BC) < k
    total = fresh_start + c_rest
    print(f"coordinates used: {total} <= N={N}  -> WINDOW COMBINATORIALLY FEASIBLE")
    return True


# ---------------------------------------------------------------- Part B core


def balanced_ok(rp, t, singles, Tm1, n):
    """rp = [r12only, r13only, r23only] exactly-two-coincidence counts,
    t = triple coincidences, singles = coords with all three g_i distinct.
    Max |A_i| = (pairs containing i) + t + (singles assigned to i).
    Feasible iff we can hit |A_i| >= Tm1 for all i simultaneously.
    Greedy LP: each pair-coord gives +1 to two A's; triple gives +1 to all three;
    single gives +1 to one.  Need vector (Tm1,Tm1,Tm1) coverable."""
    r12, r13, r23 = rp
    need = []
    base = [r12 + r13 + t, r12 + r23 + t, r13 + r23 + t]
    deficit = sum(max(0, Tm1 - b) for b in base)
    return deficit <= singles, base, deficit


def eval_config(p, dom, f, g):
    """f,g coefficient arrays mod p; returns (r_f, r_g, r_fg, t, W) on dom."""
    x = np.array(dom, dtype=np.int64)
    fv = np.zeros_like(x)
    for c in f[::-1]:
        fv = (fv * x + c) % p
    gv = np.zeros_like(x)
    for c in g[::-1]:
        gv = (gv * x + c) % p
    hv = (fv + gv) % p
    zf, zg, zh = fv == 0, gv == 0, hv == 0
    # DEGENERACY GUARD: f, g, f+g must all be nonzero polynomials (three
    # DISTINCT codewords g1,g2,g3); deg < n so "vanishes on all of mu_n" = zero.
    if zf.all() or zg.all() or zh.all():
        return 0, 0, 0, 0, -1
    t = int(np.sum(zf & zg))  # root of two differences => root of all three
    r12, r23, r13 = int(zf.sum()), int(zg.sum()), int(zh.sum())
    W = r12 + r23 + r13 - t  # coincidence mass sum_x (m(x)-1): triple = +2
    return r12, r23, r13, t, W


def poly_from_roots(p, roots, scalar=1):
    c = np.array([scalar % p], dtype=object)
    coeffs = [scalar % p]
    for r in roots:
        # multiply by (x - r)
        new = [0] * (len(coeffs) + 1)
        for i, a in enumerate(coeffs):
            new[i + 1] = (new[i + 1] + a) % p
            new[i] = (new[i] - a * r) % p
        coeffs = new
    return coeffs


def shape(n):
    k = n // 4
    Tm1 = (53 * n) // 96
    demand = 3 * Tm1 - n
    cap = 3 * (k - 1)
    return k, Tm1, demand, cap


# ---------------------------------------------------------------- Part B: n=16 exhaustive


def part_b_n16():
    p, n = 17, 16
    k, Tm1, demand, cap = shape(n)
    print(f"\n== Part B: n=16, F_17, deg<={k - 1}, T-1={Tm1}, "
          f"demand W>={demand}, cap {cap} ==")
    dom = list(range(1, 17))
    best = (-1, None)
    # exhaust ALL polys of degree <= 3 for f (mod joint scaling: fix f monic or
    # lower-degree monic; g arbitrary).  f: monic with any 0..3 roots pattern ->
    # just enumerate all monic deg<=3 polys (17^3 + 17^2 + 17 + 1 small) times all
    # g (17^4) is 1.4e8*... too big; but exhaust f monic deg<=3 (4913+289+17+1)
    # and g fully-split-in-mu deg 3 with scalar (560*16) using numpy: 5220*8960
    # evals of 16 pts ~ 7.5e8 -> chunked numpy, ok.  To be safe about missing
    # non-split g, note max W needs r(g)>=demand-2*(k-1)=2, and any poly with
    # >=2 roots in mu is (x-a)(x-b)(x-c') or scalar*(x-a)(x-b): enumerate those too.
    x = np.array(dom, dtype=np.int64)
    monic_f = []
    for deg in range(0, 4):
        for tail in itertools.product(range(p), repeat=deg):
            monic_f.append(list(tail) + [1])
    fvals = []
    for f in monic_f:
        v = np.zeros_like(x)
        for c in f[::-1]:
            v = (v * x + c) % p
        fvals.append(v)
    fvals = np.array(fvals)  # (F,16)
    zf = (fvals == 0).sum(axis=1)
    gs = []
    for deg in range(0, 4):
        for tail in itertools.product(range(p), repeat=deg):
            for lead in range(1, p):
                gs.append(list(tail) + [lead])
    gs_chunk = 4000
    gvals_all = []
    for i in range(0, len(gs), gs_chunk):
        chunk = gs[i:i + gs_chunk]
        vv = np.zeros((len(chunk), 16), dtype=np.int64)
        for j, gcoef in enumerate(chunk):
            v = np.zeros_like(x)
            for c in gcoef[::-1]:
                v = (v * x + c) % p
            vv[j] = v
        gvals_all.append(vv)
    gvals = np.concatenate(gvals_all)
    zg = (gvals == 0).sum(axis=1)
    # keep only g with >=1 root (else W small) to cut size
    keep = zg >= 1
    gvals_k, zg_k = gvals[keep], zg[keep]
    print(f"f candidates {len(fvals)}, g candidates kept {len(gvals_k)}")
    bestW = -1
    best_info = None
    for i in range(len(fvals)):
        if zf[i] == 16:
            continue  # f == 0 impossible for monic, but guard
        hv = (fvals[i][None, :] + gvals_k) % p
        zh = (hv == 0).sum(axis=1)
        tt = ((fvals[i] == 0)[None, :] & (gvals_k == 0)).sum(axis=1)
        W = zf[i] + zg_k + zh - tt
        W[zh == 16] = -1  # f+g identically zero on mu_16 => g1 = g3, invalid
        j = int(np.argmax(W))
        if W[j] > bestW:
            bestW = int(W[j])
            best_info = (i, j, int(zf[i]), int(zg_k[j]), int(zh[j]), int(tt[j]))
    i, j, rf, rg, rh, t = best_info
    print(f"n=16 EXHAUSTIVE max W = {bestW} (rf={rf}, rg={rg}, rh={rh}, t={t}); "
          f"demand {demand}, cap {cap}")
    print("  verdict:", "REACHES demand" if bestW >= demand else "FALLS SHORT of demand")
    return bestW, demand


# ---------------------------------------------------------------- Part B: random/structured search


def search_random(p, n, tries, rng, target=None, verbose=True):
    k, Tm1, demand, cap = shape(n)
    # domain mu_n in F_p
    gpow = None
    for gcand in range(2, p):
        if pow(gcand, (p - 1), p) == 1:
            # find generator of F_p^*
            ok = all(pow(gcand, (p - 1) // q, p) != 1
                     for q in prime_factors(p - 1))
            if ok:
                gpow = gcand
                break
    zeta = pow(gpow, (p - 1) // n, p)
    dom = [pow(zeta, i, p) for i in range(n)]
    assert len(set(dom)) == n
    bestW = -1
    best = None
    d = k - 1
    for _ in range(tries):
        roots_f = rng.sample(dom, d)
        roots_g = rng.sample(dom, d)
        sf = rng.randrange(1, p)
        sg = rng.randrange(1, p)
        f = poly_from_roots(p, roots_f, sf)
        g = poly_from_roots(p, roots_g, sg)
        r12, r23, r13, t, W = eval_config(p, dom, f, g)
        if W > bestW:
            bestW = W
            best = (r12, r23, r13, t)
    if verbose:
        print(f"  random fully-split ({tries} tries): best W={bestW} {best} "
              f"vs demand {demand}, cap {cap}")
    return bestW, best, dom


def prime_factors(m):
    fs = set()
    dd = 2
    while dd * dd <= m:
        while m % dd == 0:
            fs.add(dd)
            m //= dd
        dd += 1
    if m > 1:
        fs.add(m)
    return fs


def search_structured_subgroup(p, n, m):
    """f = F(x^d), g = G(x^d) with d = n//m; F,G best pair found at scale m by
    inner search; roots multiply by d."""
    k, Tm1, demand, cap = shape(n)
    d = n // m
    km, Tm1m, demandm, capm = shape(m)
    # inner degree budget: floor((k-1)/d) = m/4 - 1 (= km - 1). good.
    assert (k - 1) // d == km - 1
    return d, demandm, capm


def hillclimb(p, n, dom, iters, rng, init=None):
    k, Tm1, demand, cap = shape(n)
    d = k - 1
    if init is None:
        roots_f = rng.sample(dom, d)
        roots_g = rng.sample(dom, d)
        sf, sg = 1, 1
    else:
        roots_f, roots_g, sf, sg = init
    f = poly_from_roots(p, roots_f, sf)
    g = poly_from_roots(p, roots_g, sg)
    cur = eval_config(p, dom, f, g)[4]
    for _ in range(iters):
        which = rng.random() < 0.5
        roots = roots_f if which else roots_g
        i = rng.randrange(d)
        newroot = rng.choice(dom)
        old = roots[i]
        roots[i] = newroot
        scl = rng.randrange(1, p) if rng.random() < 0.1 else (sf if which else sg)
        if which:
            f2 = poly_from_roots(p, roots, scl)
            W = eval_config(p, dom, f2, g)[4]
        else:
            g2 = poly_from_roots(p, roots, scl)
            W = eval_config(p, dom, f, g2)[4]
        if W >= cur:
            cur = W
            if which:
                sf = scl
                f = poly_from_roots(p, roots, sf)
            else:
                sg = scl
                g = poly_from_roots(p, roots, sg)
        else:
            roots[i] = old
    return cur, (roots_f, roots_g, sf, sg)


def part_b_scaled():
    rng = random.Random(466)
    results = {}
    for (p, n, tries, hc) in [(97, 32, 4000, 6000), (193, 64, 2000, 8000),
                              (257, 256, 400, 4000)]:
        k, Tm1, demand, cap = shape(n)
        print(f"\n== Part B: n={n}, F_{p}, deg<={k - 1}, T-1={Tm1}, "
              f"demand {demand}, cap {cap} ==")
        bw, best, dom = search_random(p, n, tries, rng)
        hw, state = hillclimb(p, n, dom, hc, rng)
        for _ in range(3):
            hw2, state = hillclimb(p, n, dom, hc, rng, init=state)
            hw = max(hw, hw2)
        print(f"  hill-climb best W = {hw} vs demand {demand}")
        # structured: coset polynomials x^a - c products
        sw = structured_coset_search(p, n, dom, rng)
        print(f"  structured coset-product best W = {sw} vs demand {demand}")
        results[n] = (max(bw, hw, sw), demand, cap)
    return results


def structured_coset_search(p, n, dom, rng):
    """f, g = products of (x^a - c_j) with a | n, total degree <= k-1;
    then f+g evaluated.  Also try f,g as F(x^a), G(x^a) with F,G found greedily
    at scale n//a."""
    k, _, demand, cap = shape(n)
    d = k - 1
    best = -1
    domset = set(dom)
    zeta_n = dom[1]
    for a in [w for w in (2, 4, 8, 16) if n % w == 0 and w <= d]:
        s = d // a  # number of coset factors
        m = n // a
        # subdomain mu_m = {x^a : x in mu_n}
        sub = sorted({pow(x, a, p) for x in dom})
        # inner problem: F,G deg <= s over mu_m maximize W_inner; roots scale by a
        rng2 = random.Random(a * 7919)
        bi = -1
        for _ in range(1500):
            rf = rng2.sample(sub, min(s, m))
            rgt = rng2.sample(sub, min(s, m))
            F = poly_from_roots(p, rf, rng2.randrange(1, p))
            G = poly_from_roots(p, rgt, rng2.randrange(1, p))
            _, _, _, _, W = eval_config(p, sub, F, G)
            if W > bi:
                bi = W
                bF, bG = F, G
        # lift: f(x) = F(x^a)
        f = lift_pow(bF, a)
        g = lift_pow(bG, a)
        r12, r23, r13, t, W = eval_config(p, dom, f, g)
        if W > best:
            best = W
    return best


def lift_pow(F, a):
    out = [0] * ((len(F) - 1) * a + 1)
    for i, c in enumerate(F):
        out[i * a] = c
    return out


if __name__ == "__main__":
    part_a()
    b16, d16 = part_b_n16()
    res = part_b_scaled()
    print("\n== SUMMARY ==")
    print(f"Part A: window combinatorially FEASIBLE (explicit intervals).")
    print(f"n=16 exhaustive: max W {b16} vs demand {d16} -> "
          f"{'REALIZED' if b16 >= d16 else 'NOT REALIZED'}")
    for n, (w, dem, cap) in res.items():
        print(f"n={n}: best W {w} vs demand {dem} (cap {cap}) -> "
              f"{'REALIZED' if w >= dem else 'search fell short'}")
