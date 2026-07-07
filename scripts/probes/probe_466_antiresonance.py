#!/usr/bin/env python3
"""probe_466_antiresonance.py -- LANE P1 (issue #466, dossier v3 sec 6 Tier-2, never run).

QUESTION: does the WORST frequency b* (achieving M = max_{b!=0}|eta_b|, where
eta_b = sum_{x in mu_n} e(b x / p)) sit in an "anti-resonant" class that a
Ramanujan-sum / resonance dichotomy (Chapman-Mudgal 2605.15434 shape) could
exploit, or are resonance statistics b-blind under the mu_n dilation symmetry?

METHOD.  |eta_b| is EXACTLY constant on dilation cosets b*mu_n (for u in mu_n,
eta_{ub} = sum_x e(ubx/p) = eta_b by reindexing x -> u^{-1}x); we VERIFY this
numerically, then work per-coset.  Cosets are enumerated as b_j = g^j,
j = 0..m-1, m = (p-1)/n, g a primitive root; coset j = {g^{j+km} : k}.
"Resonance statistics of b*" = statistics of the worst coset, compared against
the EXACT empirical distribution over all m cosets (percentile rank).

Per-coset statistics:
  (a) multiplicative / gcd structure:
      - min_mult_order : min over coset of mult. order of b mod p
                         = (p-1)/max_k gcd(j+km, p-1)
      - quot_order     : canonical order of the coset in F_p^x / mu_n
                         = m/gcd(j,m)   (generator-independent)
      - max_gcd_b_pm1  : max over coset of gcd(b, p-1)  (additive gcd structure)
  (b) Ramanujan sums c_q(b) = mu(q/gcd(b,q)) phi(q)/phi(q/gcd(b,q)), small q:
      - mean_cq_<q>    : coset-mean of c_q(b)
      - plus EXACT full-b Pearson corr(|eta_b|, c_q(b)) over ALL b in 1..p-1
        (computed from per-coset first/second moments; no length-p array needed)
  (c) qr_frac          : fraction of coset that are quadratic residues
                         (analytic: b = g^{j+km} is QR iff j+km even; if m even
                         the coset is all-QR or all-NQR by parity of j; if m odd
                         the fraction is identically 1/2 -> degenerate)
  (d) diophantine / major-arc resonance:
      - min_freq_norm  : min over coset of ||b/p||  (low-frequency resonance)
      - dioph_Q32      : min over coset and 1<=q<=32 of ||q b / p||
                         (classical resonance / major-arc membership statistic)

DECISION RULE (lane spec): if the worst coset's statistics are indistinguishable
from a random coset (percentiles ~ uniform across all (n,p) runs, no consistent
extreme) -> REFUTED (b-blind; the dichotomy cannot split the sup over b).
If the worst coset is consistently extreme in some named statistic across primes
and sizes -> LIVE.

REGIME DISCIPLINE (#400 trap): p prime, p = 1 mod n, p >= n^4 (beta >= 4),
mu_n a PROPER subgroup (automatic since p-1 >= n^4 - 1 > n), never n = p-1,
>= 2 primes per n, n in {8,16,32,64} (>= 2 octaves).

Run:  python scripts/probes/probe_466_antiresonance.py
"""

import sys
import math
import numpy as np
from math import gcd

# ----------------------------------------------------------------------------
# number theory helpers
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


def phi(n: int) -> int:
    r = n
    for q in factorize(n):
        r -= r // q
    return r


def mobius(n: int) -> int:
    fs = factorize(n)
    if any(e > 1 for e in fs.values()):
        return 0
    return -1 if len(fs) % 2 else 1


def ramanujan_table(q: int) -> np.ndarray:
    """c_q(b) as a function of b mod q (length-q lookup table)."""
    tab = np.empty(q, dtype=np.float64)
    for r in range(q):
        g = gcd(r, q)
        qq = q // g
        tab[r] = mobius(qq) * phi(q) / phi(qq)
    return tab


def primes_for(n: int, count: int):
    """First `count` primes p >= n^4 with p = 1 mod n."""
    out = []
    p = n ** 4
    p += (1 - p) % n  # smallest >= n^4 with p = 1 mod n
    while len(out) < count:
        if is_prime(p):
            out.append(p)
        p += n
    return out


# ----------------------------------------------------------------------------
# core per-(n,p) computation
# ----------------------------------------------------------------------------

QLIST = [2, 3, 4, 5, 6, 7, 8, 9, 12, 16]   # Ramanujan moduli
QMAX_DIOPH = 32                            # diophantine resonance depth
CHUNK = 32768                              # rows of the coset matrix per chunk


def analyze(n: int, p: int, rng: np.random.Generator):
    m = (p - 1) // n
    g = primitive_root(p)
    h = pow(g, m, p)                       # generator of mu_n
    X = np.empty(n, dtype=np.int64)        # mu_n elements
    x = 1
    for k in range(n):
        X[k] = x
        x = x * h % p
    B = np.empty(m, dtype=np.int64)        # coset reps g^j
    b = 1
    for j in range(m):
        B[j] = b
        b = b * g % p

    ram = {q: ramanujan_table(q) for q in QLIST}

    abs_eta = np.empty(m)
    minord = np.empty(m, dtype=np.int64)
    maxgcd = np.empty(m, dtype=np.int64)
    minfreq = np.empty(m, dtype=np.int64)      # min ||b||_p (integer distance)
    dioph = np.empty(m, dtype=np.int64)        # min over q<=32 of ||q b||_p
    meancq = {q: np.empty(m) for q in QLIST}
    meancq2 = {q: np.empty(m) for q in QLIST}

    K = np.arange(n, dtype=np.int64)
    two_pi_over_p = 2.0 * np.pi / p

    for lo in range(0, m, CHUNK):
        hi = min(lo + CHUNK, m)
        E = (B[lo:hi, None] * X[None, :]) % p          # coset elements
        # eta
        c = np.exp(1j * (two_pi_over_p * E))
        abs_eta[lo:hi] = np.abs(c.sum(axis=1))
        del c
        # (a) orders
        dl = np.arange(lo, hi, dtype=np.int64)[:, None] + m * K[None, :]
        gmax = np.gcd(dl, p - 1).max(axis=1)
        minord[lo:hi] = (p - 1) // gmax
        maxgcd[lo:hi] = np.gcd(E, p - 1).max(axis=1)
        # (b) Ramanujan coset means
        for q in QLIST:
            v = ram[q][(E % q)]
            meancq[q][lo:hi] = v.mean(axis=1)
            meancq2[q][lo:hi] = (v * v).mean(axis=1)
        # (d) diophantine
        d1 = np.minimum(E, p - E)
        minfreq[lo:hi] = d1.min(axis=1)
        dmin = d1.copy()
        for q in range(2, QMAX_DIOPH + 1):
            t = (E * q) % p
            np.minimum(t, p - t, out=t)
            np.minimum(dmin, t, out=dmin)
        dioph[lo:hi] = dmin.min(axis=1)
        del E, d1, dmin

    # Parseval check: sum_{b!=0} |eta_b|^2 = n(p-n)  <=>  sum_j |eta_j|^2 = p-n
    parseval_rel = abs(n * float((abs_eta ** 2).sum()) - n * (p - n)) / (n * (p - n))

    # coset-constancy spot check (3 random cosets, all n elements directly)
    const_dev = 0.0
    for j in rng.choice(m, size=3, replace=False):
        elems = (int(B[j]) * X) % p
        vals = []
        for e in elems:
            vals.append(abs(np.exp(1j * two_pi_over_p * ((e * X) % p)).sum()))
        vals = np.array(vals)
        const_dev = max(const_dev, float(vals.max() - vals.min()) / float(vals.mean()))

    # quotient-group order (canonical) and QR fraction (analytic)
    J = np.arange(m, dtype=np.int64)
    gcdjm = np.gcd(J, m)
    quot_ord = m // gcdjm
    if m % 2 == 0:
        qr_frac = 1.0 - (J % 2).astype(np.float64)   # all-QR iff j even
        qr_degenerate = False
    else:
        qr_frac = np.full(m, 0.5)
        qr_degenerate = True

    stats = {
        "min_mult_order": minord.astype(np.float64),
        "quot_order": quot_ord.astype(np.float64),
        "max_gcd_b_pm1": maxgcd.astype(np.float64),
        "min_freq_norm": minfreq.astype(np.float64) / p,
        "dioph_Q32": dioph.astype(np.float64) / p,
        "qr_frac": qr_frac,
    }
    for q in QLIST:
        stats[f"mean_c{q}"] = meancq[q]

    jstar = int(np.argmax(abs_eta))
    M = float(abs_eta[jstar])
    C = M / math.sqrt(n * math.log(p / n))

    # exact full-b Pearson corr(|eta_b|, c_q(b)) over all b in 1..p-1,
    # from per-coset moments (|eta| coset-constant, coset sizes equal)
    fullcorr = {}
    Eabs = float(abs_eta.mean())
    Vabs = float((abs_eta ** 2).mean()) - Eabs ** 2
    for q in QLIST:
        Ec = float(meancq[q].mean())
        Ec2 = float(meancq2[q].mean())
        Vc = Ec2 - Ec ** 2
        Exy = float((abs_eta * meancq[q]).mean())
        fullcorr[q] = (Exy - Eabs * Ec) / math.sqrt(Vabs * Vc) if Vabs > 0 and Vc > 0 else float("nan")

    # percentiles (midrank) of the worst coset within the exact coset distribution
    def pct(arr, v):
        return (float((arr < v).sum()) + 0.5 * float((arr == v).sum())) / len(arr)

    worst_pct = {name: pct(arr, arr[jstar]) for name, arr in stats.items()}

    # top-10 cosets by |eta|: mean percentile per stat (robustness beyond argmax)
    top10 = np.argsort(abs_eta)[-10:]
    top10_pct = {name: float(np.mean([pct(arr, arr[j]) for j in top10]))
                 for name, arr in stats.items()}

    # cross-coset correlation of |eta| with each stat (Pearson + Spearman)
    def pearson(a, bb):
        sa, sb = a.std(), bb.std()
        if sa == 0 or sb == 0:
            return float("nan")
        return float(((a - a.mean()) * (bb - bb.mean())).mean() / (sa * sb))

    def spearman(a, bb):
        ra = np.argsort(np.argsort(a)).astype(np.float64)
        rb = np.argsort(np.argsort(bb)).astype(np.float64)
        return pearson(ra, rb)

    coset_corr = {name: (pearson(abs_eta, arr), spearman(abs_eta, arr))
                  for name, arr in stats.items()}

    worst_coset_min_elem = int(minfreq[jstar])
    return dict(n=n, p=p, m=m, g=g, m_parity=("even" if m % 2 == 0 else "odd"),
                M=M, C=C, parseval_rel=parseval_rel, const_dev=const_dev,
                jstar=jstar, worst_min_elem=worst_coset_min_elem,
                top5=sorted(abs_eta)[-5:],
                worst_pct=worst_pct, top10_pct=top10_pct,
                coset_corr=coset_corr, fullcorr=fullcorr,
                qr_degenerate=qr_degenerate,
                worst_vals={name: float(arr[jstar]) for name, arr in stats.items()})


# ----------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------

def main():
    rng = np.random.default_rng(466)
    plan = [(8, 3), (16, 3), (32, 3), (64, 2)]
    runs = []
    print(f"numpy {np.__version__}; QLIST={QLIST}; QMAX_DIOPH={QMAX_DIOPH}")
    for n, cnt in plan:
        for p in primes_for(n, cnt):
            beta = math.log(p) / math.log(n)
            print(f"\n=== n={n}  p={p}  (beta={beta:.2f}, m={(p-1)//n}) ===")
            sys.stdout.flush()
            r = analyze(n, p, rng)
            runs.append(r)
            print(f"  g={r['g']}  m={r['m']} ({r['m_parity']})  "
                  f"M={r['M']:.4f}  C={r['C']:.4f}  "
                  f"Parseval_rel_err={r['parseval_rel']:.2e}  "
                  f"coset-constancy max rel dev={r['const_dev']:.2e}")
            print(f"  worst coset j*={r['jstar']}  min elem |b|={r['worst_min_elem']}  "
                  f"top5 |eta| per coset: {['%.3f' % v for v in r['top5']]}")
            print(f"  {'statistic':>16s} {'val(j*)':>12s} {'pct(j*)':>8s} "
                  f"{'top10pct':>9s} {'pearson':>8s} {'spearman':>9s}")
            for name in r["worst_pct"]:
                pe, sp = r["coset_corr"][name]
                print(f"  {name:>16s} {r['worst_vals'][name]:>12.5g} "
                      f"{r['worst_pct'][name]:>8.3f} {r['top10_pct'][name]:>9.3f} "
                      f"{pe:>8.4f} {sp:>9.4f}")
            print("  full-b Pearson corr(|eta_b|, c_q(b)): " +
                  "  ".join(f"q={q}:{r['fullcorr'][q]:+.5f}" for q in QLIST))
            sys.stdout.flush()

    # ------------------------------------------------------------------
    # aggregate verdict
    # ------------------------------------------------------------------
    print("\n" + "=" * 78)
    print("AGGREGATE: worst-coset percentile per statistic across all runs")
    print("(null hypothesis: Uniform(0,1); extreme = <=0.05 or >=0.95)")
    names = list(runs[0]["worst_pct"].keys())
    header = f"{'statistic':>16s} " + " ".join(f"{r['n']}/{str(r['p'])[-4:]}" for r in runs)
    print(header)
    verdict_live = []
    for name in names:
        pcts = [r["worst_pct"][name] for r in runs]
        lo = sum(1 for v in pcts if v <= 0.05)
        hi = sum(1 for v in pcts if v >= 0.95)
        row = f"{name:>16s} " + " ".join(f"{v:7.3f}" for v in pcts)
        flag = ""
        if lo >= 0.75 * len(runs):
            flag = f"  << CONSISTENTLY LOW ({lo}/{len(runs)})"
            verdict_live.append((name, "low", lo, len(runs)))
        elif hi >= 0.75 * len(runs):
            flag = f"  << CONSISTENTLY HIGH ({hi}/{len(runs)})"
            verdict_live.append((name, "high", hi, len(runs)))
        print(row + flag)
        mean_pct = float(np.mean(pcts))
        print(f"{'':>16s} mean={mean_pct:.3f}  n_low={lo}  n_high={hi}")

    print("\nfull-b Ramanujan correlations |corr| max over runs:")
    for q in QLIST:
        mx = max(abs(r["fullcorr"][q]) for r in runs)
        print(f"  q={q:>2d}: max |corr(|eta|,c_q)| = {mx:.5f}")

    print("\n" + "=" * 78)
    if verdict_live:
        print("VERDICT: LIVE -- worst coset consistently extreme in: " +
              ", ".join(f"{nm} ({d}, {k}/{t})" for nm, d, k, t in verdict_live))
    else:
        print("VERDICT: REFUTED (b-blind) -- the worst coset's resonance statistics")
        print("are indistinguishable from a random coset across all primes and sizes;")
        print("the resonance dichotomy has no b-structure to split the sup over.")


if __name__ == "__main__":
    main()
