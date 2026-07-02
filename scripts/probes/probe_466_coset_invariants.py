#!/usr/bin/env python3
"""probe_466_coset_invariants.py -- LANE W8 TASK A (issue #466): the coset-SET
invariant classification (round-1 P1's structural followup).

BACKGROUND.  P1 (probe_466_antiresonance) killed every RESIDUE-CLASS statistic
of the worst frequency b*: |eta_b| (eta_b = sum_{x in mu_n} e(bx/p)) depends
only on the coset C_b = b*mu_n AS A SET of residues, and the dilation symmetry
washes out every residue statistic of b.  The kill-branch conclusion: "any
future dichotomy must classify coset-SETS via arc-concentration functionals."
Related prior [doorIV-worstb-phaseset-equidistributes] (2026-06-23): the
worst-b set's consecutive-gap variance decays to Poisson as n grows -- one
spacing statistic is dead asymptotically; the FULL arc-concentration battery
and the predictive-ordering question were never run.  This probe runs them.

OBJECT.  For each of the m = (p-1)/n cosets C_j = g^j * mu_n (as point sets
T = C_j/p on the circle), a battery of SET-functionals:
  (i)   disc_j2..disc_jJ : best-arc mass EXCESS at dyadic arc lengths 2^-j
        (max over arcs anchored at points, exact), reported as the excess
        D/n - 2^-j; plus the combined z-score disc_z = max_j over scales of
        (D/n - 2^-j)/sqrt(2^-j(1-2^-j)/n).
  (ii)  w1_unif : Wasserstein-1 distance of the empirical measure to uniform
        on the circle (grid-4096 evaluation of min_c int |F(t)-t-c| dt).
  (iii) paircorr : sum over pairs 1/||(c-c')/p||  (|| || = circle distance).
  (iv)  l2arc_j : L2 arc energy at scale 2^-j  = sum_{pairs} (1 - d/2^-j)_+
        (triangular-kernel pair count = (2^j/1) * int N(x,2^-j)^2 dx up to
        affine normalization).
  (v)   dir_K : Dirichlet-kernel correlation sum_i D_K(t_i),
        D_K(t) = sin((2K+1) pi t)/sin(pi t), dyadic K.  NOTE: dir_K CONTAINS
        the target (its k=1 term is 2*eta_b since eta_b is real for even n);
        the honest predictor is the DEFLATED dirdef_K = dir_K - n - 2*eta_b
        = 2 sum_{2<=k<=K} eta at frequency kb (pure multiplicative-neighbor
        information).  Both reported, the raw one marked CONTAMINATED.
  plus  min_gap, gap_var (consecutive-gap statistics; gap_var is the
        [doorIV-worstb-phaseset-equidistributes] statistic, for continuity).

MEASURE.  Across all m cosets: Spearman rank correlation of each functional
with |eta_b|; percentile of the argmax coset j* in each functional; top-10
mean percentile; and the LOCALIZATION factor: searching cosets in decreasing
order of the functional, what fraction of the m cosets must be examined
before hitting j* (and the |eta| rank of the functional's own top coset).

COST HONESTY.  eta_b itself costs O(n) per coset; every functional here costs
O(n log n)..O(n^2) per coset, so there is NO per-coset cost saving -- the
deliverable is the LANGUAGE question (which set-functional carries the sup,
i.e. the correct alphabet for any future dichotomy) and argmax localization
(whether a structural functional confines the certificate search to a
vanishing fraction of cosets).  disc/l2arc/min_gap are transcendental-free
(integer/rational arithmetic only), which matters for certificate checking.

DECISION RULE.  LIVE: some functional (not the contaminated dir_K) has
|Spearman| >= 0.5 in ALL runs AND places j* at percentile >= 0.99 in >= 3/4
of runs.  LANGUAGE-HINT: consistent moderate |Spearman| in [0.3, 0.5) or
consistent argmax extremeness without correlation.  KILL: everything
scattered -> the coset-set language does not compress the sup either
(honest kill extending P1).

REGIME DISCIPLINE (#400 trap): p prime, p = 1 mod n, p >= n^4, mu_n PROPER,
never n = p-1, 2 generic primes per n in {16, 32}; the generalized-Fermat
prime 65537 (n = 16) run SEPARATELY and FLAGGED, never pooled.

Run:  python scripts/probes/probe_466_coset_invariants.py
"""

import sys
import math

import numpy as np

# ----------------------------------------------------------------------------
# number theory helpers (shared conventions with probe_466_antiresonance.py)
# ----------------------------------------------------------------------------

_MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize(n: int):
    fs = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        fs[n] = fs.get(n, 0) + 1
    return fs


def primitive_root(p: int) -> int:
    fac = list(factorize(p - 1).keys())
    g = 2
    while True:
        if all(pow(g, (p - 1) // r, p) != 1 for r in fac):
            return g
        g += 1


def is_generalized_fermat(p: int) -> bool:
    for e in (2, 4, 8, 16, 32):
        a = round((p - 1) ** (1.0 / e))
        for aa in (a - 1, a, a + 1):
            if aa >= 2 and aa ** e + 1 == p:
                return True
    return False


def primes_for(n: int, count: int):
    """First `count` generic (non-generalized-Fermat) primes p >= n^4, p=1 mod n."""
    out = []
    p = n ** 4
    p += (1 - p) % n
    while len(out) < count:
        if is_prime(p) and not is_generalized_fermat(p):
            out.append(p)
        p += n
    return out


# ----------------------------------------------------------------------------
# per-(n,p) functional battery
# ----------------------------------------------------------------------------

CHUNK = 2048
W1GRID = 4096
KLIST = [2, 4, 8, 16, 32, 64]


def analyze(n: int, p: int, flagged: bool):
    m = (p - 1) // n
    g = primitive_root(p)
    h = pow(g, m, p)
    X = np.empty(n, dtype=np.int64)
    x = 1
    for k in range(n):
        X[k] = x
        x = x * h % p
    B = np.empty(m, dtype=np.int64)
    b = 1
    for j in range(m):
        B[j] = b
        b = b * g % p

    jmax = int(math.log2(n)) + 2
    scales = list(range(2, jmax + 1))            # arc lengths 2^-j

    abs_eta = np.empty(m)
    eta_signed = np.empty(m)                     # eta is real (n even)
    max_imag = 0.0
    disc = {j: np.empty(m) for j in scales}      # best-arc excess
    l2arc = {j: np.empty(m) for j in scales}
    w1 = np.empty(m)
    pair = np.empty(m)
    dirK = {K: np.empty(m) for K in KLIST}
    min_gap = np.empty(m)
    gap_var = np.empty(m)

    grid = (np.arange(W1GRID) + 0.5) / W1GRID

    for lo in range(0, m, CHUNK):
        hi = min(lo + CHUNK, m)
        E = (B[lo:hi, None] * X[None, :]) % p
        T = np.sort(E.astype(np.float64) / p, axis=1)     # (c, n) sorted
        c = T.shape[0]

        # eta
        z = np.exp(2j * np.pi * T).sum(axis=1)
        abs_eta[lo:hi] = np.abs(z)
        eta_signed[lo:hi] = z.real
        max_imag = max(max_imag, float(np.abs(z.imag).max()))

        # gaps
        gaps = np.diff(np.concatenate([T, T[:, :1] + 1.0], axis=1), axis=1)
        min_gap[lo:hi] = gaps.min(axis=1) * n
        gap_var[lo:hi] = (gaps * n).var(axis=1)

        # arc discrepancy: arcs anchored at points, exact for point-anchored sup
        Text = np.concatenate([T, T + 1.0], axis=1)       # (c, 2n)
        for j in scales:
            L = 2.0 ** (-j)
            # count[k, i] = #points in [T_i, T_i + L)
            cnt = (Text[:, None, :] < (T[:, :, None] + L)).sum(axis=2) \
                - np.arange(n)[None, :]
            disc[j][lo:hi] = cnt.max(axis=1) / n - L

        # pairwise circle distances
        D = np.abs(T[:, :, None] - T[:, None, :])
        D = np.minimum(D, 1.0 - D)
        iu = np.triu_indices(n, 1)
        Dp = D[:, iu[0], iu[1]]                           # (c, n(n-1)/2)
        pair[lo:hi] = (1.0 / Dp).sum(axis=1)
        for j in scales:
            L = 2.0 ** (-j)
            l2arc[j][lo:hi] = np.maximum(0.0, 1.0 - Dp / L).sum(axis=1)
        del D, Dp

        # W1 to uniform (grid): H(u) = F(u) - u; W1 = mean |H - median(H)|
        # F via searchsorted-equivalent: counts of T <= grid point
        idx = np.searchsorted(
            np.ascontiguousarray(T), grid[None, :].repeat(c, axis=0),
            side="right") if False else None
        # vectorized histogram-cumsum instead:
        bins = np.clip((T * W1GRID).astype(np.int64), 0, W1GRID - 1)
        Hcnt = np.zeros((c, W1GRID), dtype=np.int64)
        rows = np.repeat(np.arange(c), n)
        np.add.at(Hcnt, (rows, bins.ravel()), 1)
        F = np.cumsum(Hcnt, axis=1) / n                   # F at right bin edges
        H = F - (np.arange(1, W1GRID + 1) / W1GRID)[None, :]
        med = np.median(H, axis=1, keepdims=True)
        w1[lo:hi] = np.abs(H - med).mean(axis=1)
        del Hcnt, F, H

        # Dirichlet-kernel correlations (closed form)
        sinpit = np.sin(np.pi * T)
        for K in KLIST:
            dirK[K][lo:hi] = (np.sin((2 * K + 1) * np.pi * T) / sinpit).sum(axis=1)
        del E, T, Text, gaps, sinpit

    # sanity: eta real; Parseval
    parseval_rel = abs(float((abs_eta ** 2).sum()) - (p - n)) / (p - n)

    disc_z = np.max(np.stack(
        [(disc[j]) / math.sqrt(2.0 ** (-j) * (1 - 2.0 ** (-j)) / n)
         for j in scales]), axis=0)

    stats = {}
    for j in scales:
        stats[f"disc_2^-{j}"] = disc[j]
    stats["disc_z"] = disc_z
    stats["w1_unif"] = w1
    stats["paircorr"] = pair
    for j in scales:
        stats[f"l2arc_2^-{j}"] = l2arc[j]
    for K in KLIST:
        stats[f"dir_{K} [CONTAM]"] = dirK[K]
    for K in KLIST:
        stats[f"dirdef_{K}"] = dirK[K] - n - 2.0 * eta_signed
    stats["|dirdef_32|"] = np.abs(dirK[32] - n - 2.0 * eta_signed)
    stats["min_gap"] = min_gap
    stats["gap_var"] = gap_var

    jstar = int(np.argmax(abs_eta))
    M = float(abs_eta[jstar])

    def pct(arr, v):
        return (float((arr < v).sum()) + 0.5 * float((arr == v).sum())) / len(arr)

    def pearson(a, bb):
        sa, sb = a.std(), bb.std()
        if sa == 0 or sb == 0:
            return float("nan")
        return float(((a - a.mean()) * (bb - bb.mean())).mean() / (sa * sb))

    def spearman(a, bb):
        ra = np.argsort(np.argsort(a)).astype(np.float64)
        rb = np.argsort(np.argsort(bb)).astype(np.float64)
        return pearson(ra, rb)

    top10 = np.argsort(abs_eta)[-10:]
    res = {}
    for name, arr in stats.items():
        sp = spearman(abs_eta, arr)
        # orient so that larger oriented-value should mean larger |eta|
        arr_o = arr if (not math.isnan(sp) and sp >= 0) else -arr
        order = np.argsort(-arr_o)                       # best-first search order
        loc = (int(np.where(order == jstar)[0][0]) + 1) / m
        # |eta| percentile of the functional's own argmax coset
        own = pct(abs_eta, abs_eta[int(order[0])])
        res[name] = dict(
            spearman=sp,
            pct_jstar=pct(arr, arr[jstar]),
            top10_pct=float(np.mean([pct(arr, arr[j]) for j in top10])),
            localize=loc,
            own_top_eta_pct=own,
        )

    return dict(n=n, p=p, m=m, g=g, flagged=flagged, M=M,
                C=M / math.sqrt(n * math.log(p / n)),
                parseval_rel=parseval_rel, max_imag=max_imag,
                jstar=jstar, res=res, names=list(stats.keys()))


# ----------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------

def main():
    runs = []
    print("probe_466_coset_invariants -- W8/A: coset-SET arc-concentration battery")
    print(f"numpy {np.__version__}; W1 grid {W1GRID}; Dirichlet K {KLIST}")
    plan = []
    for n in (16, 32):
        for p in primes_for(n, 2):
            plan.append((n, p, False))
    plan.append((16, 65537, True))       # generalized-Fermat, FLAGGED, not pooled

    for (n, p, flagged) in plan:
        beta = math.log(p) / math.log(n)
        tag = "  ** FLAGGED (generalized-Fermat; excluded from verdict) **" if flagged else ""
        print(f"\n=== n={n}  p={p}  (beta={beta:.2f}, m={(p-1)//n}){tag} ===")
        sys.stdout.flush()
        r = analyze(n, p, flagged)
        runs.append(r)
        print(f"  g={r['g']}  M={r['M']:.4f}  C={r['C']:.4f}  "
              f"Parseval_rel={r['parseval_rel']:.2e}  max|Im eta|={r['max_imag']:.2e}")
        print(f"  {'functional':>16s} {'spearman':>9s} {'pct(j*)':>8s} "
              f"{'top10pct':>9s} {'localize':>9s} {'ownTopEta':>10s}")
        for name in r["names"]:
            d = r["res"][name]
            print(f"  {name:>16s} {d['spearman']:>9.4f} {d['pct_jstar']:>8.3f} "
                  f"{d['top10_pct']:>9.3f} {d['localize']:>9.4f} "
                  f"{d['own_top_eta_pct']:>10.4f}")
        sys.stdout.flush()

    # ------------------------------------------------------------------
    # aggregate verdict over GENERIC runs only
    # ------------------------------------------------------------------
    gen = [r for r in runs if not r["flagged"]]
    names = gen[0]["names"]
    print("\n" + "=" * 78)
    print("AGGREGATE over generic runs (flagged GF run excluded)")
    print(f"{'functional':>16s} {'min|sp|':>8s} {'max|sp|':>8s} "
          f"{'#pct>=.99':>9s} {'#pct<=.01':>9s} {'worst-localize':>14s}")
    live, hint = [], []
    for name in names:
        sps = [gen_r["res"][name]["spearman"] for gen_r in gen]
        pcts = [gen_r["res"][name]["pct_jstar"] for gen_r in gen]
        locs = [gen_r["res"][name]["localize"] for gen_r in gen]
        aspmin = min(abs(v) for v in sps)
        aspmax = max(abs(v) for v in sps)
        nhi = sum(1 for v in pcts if v >= 0.99)
        nlo = sum(1 for v in pcts if v <= 0.01)
        print(f"{name:>16s} {aspmin:>8.4f} {aspmax:>8.4f} {nhi:>9d} {nlo:>9d} "
              f"{max(locs):>14.4f}")
        contaminated = "CONTAM" in name
        if not contaminated:
            if aspmin >= 0.5 and (nhi + nlo) >= 0.75 * len(gen):
                live.append(name)
            elif aspmin >= 0.3 or (nhi + nlo) >= 0.75 * len(gen):
                hint.append(name)

    print("\n" + "=" * 78)
    if live:
        print("VERDICT: LIVE -- predictive coset-set functional(s): " + ", ".join(live))
    elif hint:
        print("VERDICT: LANGUAGE-HINT (no certificate) -- moderate but consistent: "
              + ", ".join(hint))
        print("No functional both predicts |eta| (|sp|>=0.5 everywhere) and pins the")
        print("argmax; the coset-set language correlates but does not compress the sup.")
    else:
        print("VERDICT: KILL -- no arc-concentration set-functional predicts |eta_b|")
        print("or localizes the argmax; extending P1: the coset-SET language does not")
        print("compress the sup either. The worst coset is invisible to arc geometry.")


if __name__ == "__main__":
    main()
