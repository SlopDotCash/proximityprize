#!/usr/bin/env python3
"""G97 probe: combinatorial discrepancy of the arc x dilate incidence system vs the
specific-set measure discrepancy of b*mu_n that the G80Z consumer needs.

Objects, for prime p, n | p-1, mu_n = order-n subgroup of F_p^*:
  (ii) SPECIFIC measure discrepancy  D(b) = sup_t |#{x in mu_n : val(bx) < t} - n t / p|
       (Kolmogorov / all-intervals form; arcs at any scale K are differences of two of
       these prefixes, so D controls every arc deviation up to factor 2).
  (i)  SYSTEM hereditary-discrepancy proxies for the incidence matrix
       M[(j,b), x] = 1 iff val(b x) in arc_j   (K arcs x k dilate-coset rows, n columns):
       - detlb  = max over sampled square submatrices |det|^(1/k)   (LSV: herdisc >= detlb/2)
       - gamma2 trace-norm lower bound  ||M||_Sigma / sqrt(rows*cols)  (gamma2 >= this;
         MNT: herdisc <~ gamma2 * log)
       - local-search upper bound on the red-blue discrepancy disc(M) (min over +-1
         colorings of mu_n of max row |sum|) -> upper bound on what colorings can do.
  KEY EXPERIMENT: is D(b*mu_n) governed by the system's herdisc (transference plausible)
  or does the specific set escape it? Compare D over all dilate cosets vs random n-sets,
  and both vs sqrt(n log p) and vs the herdisc proxies.
"""
import numpy as np
from math import sqrt, log
rng = np.random.default_rng(20260710)

def primitive_root(p):
    fac = []
    m = p - 1; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise ValueError

def mu_subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    out, x = [], 1
    for _ in range(n):
        out.append(x); x = (x * h) % p
    assert len(set(out)) == n
    return np.array(sorted(out)), g

def kolmogorov_dev(vals, p):
    """sup_t |#{v < t} - n t/p| over t in [0,p], vals = sorted residues in [0,p)."""
    n = len(vals)
    v = np.sort(vals).astype(float)
    i = np.arange(n)
    # just below each point: count=i at t=v_i ; just above: count=i+1 at t=v_i (+eps)
    d1 = np.abs(i - n * v / p)
    d2 = np.abs((i + 1) - n * v / p)
    return max(d1.max(), d2.max())

def coset_reps(p, n, g):
    k = (p - 1) // n
    return [pow(g, i, p) for i in range(k)]

def build_incidence(p, n, K, reps, mu):
    """rows = (arc j, dilate b) for b in reps, cols = mu elements. arc_j = {t : j*p <= K*t < (j+1)*p}."""
    rows = []
    for b in reps:
        vals = (b * mu) % p
        arc = (K * vals) // p          # arcIndex, exactly the consumer's floor
        for j in range(K):
            rows.append((arc == j).astype(np.int8))
    return np.array(rows, dtype=np.int8)

def detlb(M, tries=400):
    r, c = M.shape
    best = 0.0
    for k in [2, 3, 4, 6, 8, 12, 16, 24, 32]:
        if k > min(r, c): break
        bk = 0.0
        for _ in range(tries):
            ri = rng.choice(r, k, replace=False)
            ci = rng.choice(c, k, replace=False)
            d = abs(np.linalg.det(M[np.ix_(ri, ci)].astype(float)))
            if d > bk: bk = d
        if bk > 0: best = max(best, bk ** (1.0 / k))
    return best

def gamma2_tracelb(M):
    s = np.linalg.svd(M.astype(float), compute_uv=False)
    r, c = M.shape
    return s.sum() / sqrt(r * c)

def disc_local_search(M, restarts=8, iters=4000):
    """upper bound on min_chi max_row |M chi| by greedy flips."""
    r, c = M.shape
    Mf = M.astype(np.int32)
    best = None
    for _ in range(restarts):
        chi = rng.choice([-1, 1], c).astype(np.int32)
        rs = Mf @ chi
        cur = np.abs(rs).max()
        for _ in range(iters):
            i = rng.integers(c)
            delta = -2 * chi[i] * Mf[:, i]
            new = np.abs(rs + delta).max()
            if new <= cur:
                chi[i] = -chi[i]; rs = rs + delta; cur = new
        best = cur if best is None else min(best, cur)
    return best

def run(p, n, n_rand=300):
    mu, g = mu_subgroup(p, n)
    k = (p - 1) // n
    reps = coset_reps(p, n, g)
    # (ii) specific-set measure discrepancy over ALL dilate cosets
    Ds = np.array([kolmogorov_dev((b * mu) % p, p) for b in reps])
    # random baseline: random n-subsets of [1, p-1]
    Dr = np.array([kolmogorov_dev(rng.choice(np.arange(1, p), n, replace=False), p)
                   for _ in range(n_rand)])
    s_nlogp = sqrt(n * log(p)); s_n = sqrt(n)
    # (i) system proxies at K ~ sqrt(n)
    K = max(2, int(round(sqrt(n))))
    kk = min(k, 40)   # cap dilate rows for matrix work
    M = build_incidence(p, n, K, reps[:kk], mu)
    dl = detlb(M)
    g2 = gamma2_tracelb(M)
    dc = disc_local_search(M)
    # measure disc of mu_n at the SAME arc scale K (what the consumer sees):
    arc_dev_mu = 0.0
    for b in reps:
        vals = (b * mu) % p
        arc = (K * vals) // p
        cnt = np.bincount(arc, minlength=K)[:K]
        arc_dev_mu = max(arc_dev_mu, np.abs(cnt - n / K).max())
    print(f"p={p:5d} n={n:4d} k={k:4d} K={K:3d} | D(b mu_n): max={Ds.max():7.2f} "
          f"med={np.median(Ds):7.2f} min={Ds.min():6.2f} | rand n-set: med={np.median(Dr):7.2f} "
          f"q95={np.quantile(Dr,0.95):7.2f}")
    print(f"    scale: sqrt(n log p)={s_nlogp:7.2f} sqrt(n)={s_n:6.2f} "
          f"| ratios D_max/sqrt(nlogp)={Ds.max()/s_nlogp:5.2f} D_med/sqrt(nlogp)={np.median(Ds)/s_nlogp:5.2f}")
    print(f"    system ({K*kk}x{n}): detlb={dl:6.3f} (herdisc>=detlb/2) gamma2_traceLB={g2:6.3f} "
          f"coloring-disc<= {dc} | arcK devs of mu_n: {arc_dev_mu:7.2f}")
    print(f"    SEPARATION: specific-set arc dev / coloring-disc-UB = "
          f"{arc_dev_mu/max(dc,1):.1f}x ; specific / detlb = {arc_dev_mu/max(dl,1e-9):.1f}x")
    return dict(p=p, n=n, Dmax=Ds.max(), Dmed=float(np.median(Ds)),
                rmed=float(np.median(Dr)), s=s_nlogp, detlb=dl, g2=g2, disc=dc, arcdev=arc_dev_mu)

print("=== G97 arc x dilate discrepancy probe ===")
print("--- fixed n=30-ish across p (dilate-count k grows) ---")
res = []
for (p, n) in [(211, 30), (211, 42), (421, 60), (421, 84), (1009, 144), (1009, 252),
               (2017, 96), (2017, 288), (4093, 132), (4093, 341)]:
    res.append(run(p, n))
print()
print("--- prefix-system sanity: interval herdisc of ANY point set is <= 1 (alternating) ---")
for trial in range(3):
    p = 1009; n = 144
    mu, g = mu_subgroup(p, n)
    b = int(rng.integers(1, p))
    vals = np.sort((b * mu) % p)
    chi = np.array([(-1) ** i for i in range(n)])   # alternate along sorted order
    pref = np.concatenate([[0], np.cumsum(chi)])
    print(f"  b={b:4d}: alternating-coloring prefix sums range [{pref.min()},{pref.max()}] "
          f"(theory: subset of {{0,1}}) -> every interval |sum|<=1")
print()
print("--- summary table ---")
print(f"{'p':>6} {'n':>5} {'D_max':>8} {'D_med':>8} {'rand_med':>9} {'sqrt(nlogp)':>11} "
      f"{'detlb':>7} {'g2LB':>7} {'discUB':>7} {'arcdev(mu)':>10}")
for r in res:
    print(f"{r['p']:>6} {r['n']:>5} {r['Dmax']:>8.2f} {r['Dmed']:>8.2f} {r['rmed']:>9.2f} "
          f"{r['s']:>11.2f} {r['detlb']:>7.3f} {r['g2']:>7.3f} {r['disc']:>7d} {r['arcdev']:>10.2f}")
