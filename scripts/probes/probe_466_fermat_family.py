#!/usr/bin/env python3
"""
probe_466_fermat_family.py -- LANE R6 (issue #466, round-1 P1 followup).

QUESTION: do 2-adically saturated primes p = c*2^k + 1 with tiny odd c
(c in {1,3,5,7,15,25}) SYSTEMATICALLY place the worst dilation coset at/near
mu_n itself and/or inflate C = M / sqrt(n * ln(p/n))?

Round-1 anomaly: at the Fermat prime p = 65537 (n=16) the worst coset IS mu_n
(b* in mu_n, percentile 1.000).  Here we test whether that is a one-prime
accident or a constructive adversarial family.

Setup (regime discipline): mu_n = PROPER subgroup of F_p^x of order n = 2^nu,
p = 1 mod n, p in [n^3, n^6] (beta swept 3..6 explicitly), n in {8,16,32},
multiple primes per class.  eta_b = sum_{x in mu_n} e_p(b x); |eta| constant
on dilation cosets b*mu_n, so we compute one value per coset (= Gauss-period
profile over the quotient F_p^x / mu_n, cyclic of order m = (p-1)/n).

Family:   p = c*2^k+1, c in {1,3,5,7,15,25}  (v2(p-1) = k, maximal 2-adic sat).
Controls: v2(p-1) = v2(n) = nu MINIMAL, i.e. (p-1)/n odd, size-matched to each
          family prime (nearest such prime) => matched beta.

Reported per prime:
  M       = max_{b != 0} |eta_b|
  C       = M / sqrt(n * ln(p/n))          (natural log; EVT normalisation)
  M/n     = saturation ratio
  j*      = discrete log of the worst coset in the quotient w.r.t. the image
            of the smallest primitive root g  (j*=0  <=>  worst coset = mu_n)
  dist    = min(j*, m-j*)  cyclic distance to the identity coset (g-dependent)
  d*      = order of the worst coset in the quotient = min d with b* in mu_{d n}
            (canonical, generator-independent "2-adic closeness" to mu_n)
  pct0    = percentile of the mu_n coset value |eta_1| among all m cosets
  minel   = smallest centered representative in the worst coset
  eta0    = eta_1 (the mu_n-coset value, real since -1 in mu_n)

DECISION (from the lane brief):
  FAMILY-REAL     if saturated family selects the mu_n coset >= 70% across n
                  with controls < 20%, OR consistent C inflation at matched beta.
  FAMILY-ARTIFACT if the 65537 behaviour does not replicate.
"""

import math
import sys
import time
from math import gcd

import numpy as np

CS = [1, 3, 5, 7, 15, 25]
NS = [8, 16, 32]
CHUNK = 1 << 21
TIE_EPS = 1e-6

MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    for sp in MR_BASES:
        if x % sp == 0:
            return x == sp
    d, r = x - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in MR_BASES:
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(r - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def factorize(x: int):
    fs = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            fs[d] = fs.get(d, 0) + 1
            x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        fs[x] = fs.get(x, 0) + 1
    return fs


def primitive_root(p: int) -> int:
    qs = list(factorize(p - 1).keys())
    g = 2
    while True:
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
        g += 1


def profile(p: int, n: int):
    """Full Gauss-period profile of mu_n in F_p: one |eta| per dilation coset."""
    m = (p - 1) // n
    g = primitive_root(p)
    w = pow(g, m, p)                       # order-n element; mu_n = <w>
    wpow = [pow(w, i, p) for i in range(n)]
    assert len(set(wpow)) == n
    c2p = 2.0 * math.pi / p
    eta0 = sum(math.cos(c2p * x) for x in wpow)   # eta_1: real (-1 in mu_n)
    a0 = abs(eta0)

    pu = np.uint64(p)
    B = min(m, CHUNK)
    base = np.empty(B, dtype=np.uint64)
    base[0] = 1
    s = 1
    while s < B:                           # base[t] = g^t mod p, doubling fill
        t = min(s, B - s)
        base[s:s + t] = (base[:t] * np.uint64(pow(g, s, p))) % pu
        s += t
    wl = [np.uint64(x) for x in wpow]

    M, jstar, etastar = -1.0, -1, 0.0
    cnt_le = 0
    top = np.zeros(0)
    for j0 in range(0, m, B):
        L = min(B, m - j0)
        Rb = (base[:L] * np.uint64(pow(g, j0, p))) % pu   # g^{j0..j0+L-1}
        acc = np.zeros(L)
        for i in range(n):
            acc += np.cos(((Rb * wl[i]) % pu).astype(np.float64) * c2p)
        aa = np.abs(acc)
        cnt_le += int(np.count_nonzero(aa <= a0 + 1e-12))
        bi = int(np.argmax(aa))
        if aa[bi] > M:
            M = float(aa[bi])
            jstar = j0 + bi
            etastar = float(acc[bi])
        k = min(64, L)
        top = np.sort(np.concatenate([top, np.partition(aa, L - k)[L - k:]]))[-64:]

    ties = int(np.count_nonzero(top >= M - TIE_EPS))
    bstar = pow(g, jstar, p)
    minel = min(min(e, p - e) for e in ((bstar * x) % p for x in wpow))
    dstar = m // gcd(jstar, m) if jstar > 0 else 1
    return dict(
        p=p, n=n, m=m, g=g, M=M,
        C=M / math.sqrt(n * math.log(p / n)),
        sat=M / n,
        jstar=jstar, dist=min(jstar, m - jstar), dstar=dstar,
        eta0=eta0, pct0=cnt_le / m, minel=minel, ties=ties,
        mu_is_worst=(jstar == 0 or a0 >= M - TIE_EPS),
        etastar=etastar,
        top5=[float(t) for t in top[-5:]],
        beta=math.log(p) / math.log(n),
    )


def saturated_primes(n: int):
    lo, hi = n ** 3, n ** 6
    nu = v2(n)
    out = []
    for c in CS:
        k = nu
        while c * (1 << k) + 1 <= hi:
            p = c * (1 << k) + 1
            if p >= lo and is_prime(p):
                out.append((p, c, k))
            k += 1
    return sorted(set(out))


def nearest_control(n: int, target: int, exclude, lo=None, hi=None) -> int:
    """Nearest prime q = n*t+1 with t ODD (v2(q-1)=v2(n) minimal), in range."""
    lo = lo if lo is not None else n ** 3
    hi = hi if hi is not None else n ** 6
    t0 = max(1, target // n)
    for dt in range(0, 400000):
        for t in (t0 - dt, t0 + dt):
            if t < 1 or t % 2 == 0:
                continue
            q = n * t + 1
            if q < lo or q > hi or q in exclude:
                continue
            if is_prime(q):
                return q
    return None


def c_deficit(B: int, terms: int = 200) -> float:
    """c_B = 2 * sum_{i>=1} (1 - cos(2 pi B^-i))  (geometric-tail deficit)."""
    s, x = 0.0, 1.0 / B
    for _ in range(terms):
        s += 2.0 * (1.0 - math.cos(2.0 * math.pi * x))
        x /= B
        if x < 1e-12:
            break
    return s


def gf_phase2():
    """PHASE 2: generalized-Fermat sub-family p = b^(2^s)+1 (b even),
    n | 2^(s+1).  Then ord_p(b) = 2^(s+1), and mu_n = <B> = {+-B^j : j < n/2}
    with B = b^(2^(s+1)/n) -- a GEOMETRIC PROGRESSION OF SMALL INTEGERS
    (B^(n/2) = p-1).  Closed form:
        eta_1 = sum_{j<n/2} 2 cos(2 pi B^j / p)  =  n - c_B + o(1),
        c_B   = 2 sum_{i>=1} (1 - cos(2 pi B^-i)),
    so M >= n - O(1) at the mu_n coset itself, and
        C -> sqrt(2/ln B) as n grows along the family (B fixed).
    """
    print("=" * 100)
    print("PHASE 2: generalized-Fermat sub-family p = b^(2^s)+1  (the c=1 mechanism, made exact)")
    print(gf_phase2.__doc__)
    rows = []
    for n in NS:
        nu = v2(n)
        lo, hi = n ** 3, n ** 6
        cands = {}
        s = nu - 1                       # smallest s with 2^(s+1) >= n
        while (1 << (1 << s)) <= hi:     # b=2 candidate fits
            e = 1 << s
            b = 2
            while b ** e + 1 <= hi:
                p = b ** e + 1
                if p > n * n and is_prime(p):   # p>n^2 keeps m>=n (proper regime)
                    cands.setdefault(p, b ** ((2 * e) // n))
                b += 2
            s += 1
        for p, B in sorted(cands.items()):
            r = profile(p, n)
            eta_exact = sum(2.0 * math.cos(2.0 * math.pi * (B ** j) / p)
                            for j in range(n // 2))
            cB = c_deficit(B)
            pred = n - cB
            inwin = lo <= p <= hi
            tag = "IN-WINDOW" if inwin else f"OUT-OF-WINDOW (beta={r['beta']:.2f})"
            print(f"  n={n:>2d} p={p:>9d} = {B}^{n//2}+1  (B={B})  {tag}")
            print(f"     measured    : eta0={r['eta0']:9.4f}  M={r['M']:9.4f}  "
                  f"muWORST={'YES' if r['mu_is_worst'] else 'no'}  pct0={r['pct0']:.4f}  "
                  f"C={r['C']:.4f}  j*={r['jstar']}  minel={r['minel']}")
            print(f"     closed form : sum 2cos(2pi B^j/p) = {eta_exact:9.4f} ; "
                  f"n - c_B = {pred:9.4f}  (c_B = {cB:.4f}) ; "
                  f"C_pred = {pred/math.sqrt(n*math.log(p/n)):.4f} ; "
                  f"C_inf = sqrt(2/ln B) = {math.sqrt(2.0/math.log(B)):.4f}")
            q = nearest_control(n, p, {p}, lo=max(n * n + 1, p // 2), hi=2 * p)
            if q is not None:
                rq = profile(q, n)
                print(f"     control     : q={q}  M={rq['M']:9.4f}  C={rq['C']:.4f}  "
                      f"pct0={rq['pct0']:.4f}  => C_gf/C_ctl = {r['C']/rq['C']:.4f}")
            rows.append((n, p, B, r, eta_exact, pred))
        print()
    ok = [t for t in rows if abs(t[3]['eta0'] - t[4]) < 1e-3]
    loc = [t for t in rows if t[3]['pct0'] >= 0.999]
    print(f"  PHASE-2 SUMMARY: {len(rows)} GF primes tested; closed-form eta_1 exact "
          f"(|err|<1e-3) for {len(ok)}/{len(rows)}; mu_n coset at percentile >=0.999 "
          f"for {len(loc)}/{len(rows)}.")
    print("  NOTE: next candidate up the b=2 tower is n=64 via F_5 = 2^32+1 = 641*6700417"
          " (COMPOSITE) -- the in-window b=2 family ends at F_4 = 65537 (n=32).")
    return rows


def fmt_row(tag, r):
    return (f"{tag:>10s} p={r['p']:>11d} beta={r['beta']:.2f} m={r['m']:>9d} "
            f"M={r['M']:8.3f} M/n={r['sat']:.4f} C={r['C']:.4f} "
            f"j*={r['jstar']:>9d} dist={r['dist']:>9d} d*={r['dstar']:>9d} "
            f"pct0={r['pct0']:.4f} eta0={r['eta0']:8.3f} minel={r['minel']:>10d} "
            f"ties={r['ties']} muWORST={'YES' if r['mu_is_worst'] else 'no'}")


def main():
    t_all = time.time()
    print(__doc__)
    print(f"numpy {np.__version__}; chunk={CHUNK}; tie_eps={TIE_EPS}")
    print("NOTE: |eta| computed once per dilation coset (constant on cosets);"
          " b=0 excluded; eta real since -1 in mu_n (n even).")
    print()

    all_sat, all_ctl, pairs = [], [], []

    for n in NS:
        nu = v2(n)
        sats = saturated_primes(n)
        print("=" * 100)
        print(f"### n = {n} (nu = {nu})  range p in [{n**3}, {n**6}]  "
              f"saturated family: {[(p, f'{c}*2^{k}+1') for p, c, k in sats]}")
        sat_rows, ctl_rows = [], []
        used = set(p for p, _, _ in sats)
        for p, c, k in sats:
            t0 = time.time()
            r = profile(p, n)
            r['c'], r['k'] = c, k
            sat_rows.append(r)
            print(fmt_row(f"SAT c={c}", r) + f"  [{time.time()-t0:.1f}s]")
            sys.stdout.flush()
            q = nearest_control(n, p, used)
            if q is None:
                print(f"   !! no control found near {p}")
                continue
            used.add(q)
            t0 = time.time()
            rq = profile(q, n)
            ctl_rows.append(rq)
            print(fmt_row("CTL", rq) +
                  f"  [{time.time()-t0:.1f}s]  (matched to p={p}, "
                  f"size ratio {q/p:.4f}, v2(q-1)={v2(q-1)})")
            sys.stdout.flush()
            pairs.append((n, r, rq))

        # ensure >= 5 controls per n (grid extras if family was small)
        extra_targets = []
        if len(ctl_rows) < 5:
            lo, hi = n ** 3, n ** 6
            for i in range(5 - len(ctl_rows)):
                extra_targets.append(int(lo * (hi / lo) ** ((i + 0.5) / 5)))
        for tgt in extra_targets:
            q = nearest_control(n, tgt, used)
            if q is None:
                continue
            used.add(q)
            rq = profile(q, n)
            ctl_rows.append(rq)
            print(fmt_row("CTL+", rq) + f"  (grid extra, v2(q-1)={v2(q-1)})")
            sys.stdout.flush()

        all_sat += [(n, r) for r in sat_rows]
        all_ctl += [(n, r) for r in ctl_rows]

        ns_mu = sum(r['mu_is_worst'] for r in sat_rows)
        nc_mu = sum(r['mu_is_worst'] for r in ctl_rows)
        print(f"--- n={n} summary: SAT mu_n-worst {ns_mu}/{len(sat_rows)}"
              f" ({ns_mu/max(1,len(sat_rows)):.2f});"
              f" CTL mu_n-worst {nc_mu}/{len(ctl_rows)}"
              f" ({nc_mu/max(1,len(ctl_rows)):.2f})")
        print(f"    SAT mean C = {np.mean([r['C'] for r in sat_rows]):.4f}"
              f" (max {max(r['C'] for r in sat_rows):.4f});"
              f" CTL mean C = {np.mean([r['C'] for r in ctl_rows]):.4f}"
              f" (max {max(r['C'] for r in ctl_rows):.4f})")
        print(f"    SAT mean pct0 = {np.mean([r['pct0'] for r in sat_rows]):.4f};"
              f" CTL mean pct0 = {np.mean([r['pct0'] for r in ctl_rows]):.4f}")
        print(f"    SAT d* values: {sorted(r['dstar'] for r in sat_rows)}")
        print(f"    CTL d* values: {sorted(r['dstar'] for r in ctl_rows)}")
        print()

    # ---------------- aggregate ----------------
    print("=" * 100)
    print("AGGREGATE")
    fs = sum(r['mu_is_worst'] for _, r in all_sat) / max(1, len(all_sat))
    fc = sum(r['mu_is_worst'] for _, r in all_ctl) / max(1, len(all_ctl))
    print(f"  worst coset == mu_n : SAT {sum(r['mu_is_worst'] for _, r in all_sat)}"
          f"/{len(all_sat)} = {fs:.3f}   CTL "
          f"{sum(r['mu_is_worst'] for _, r in all_ctl)}/{len(all_ctl)} = {fc:.3f}")
    # relaxed: mu_n coset in the top 1% (pct0 >= 0.99) or d* <= 4
    fs99 = sum(r['pct0'] >= 0.99 for _, r in all_sat) / max(1, len(all_sat))
    fc99 = sum(r['pct0'] >= 0.99 for _, r in all_ctl) / max(1, len(all_ctl))
    print(f"  mu_n coset in top 1% (pct0>=0.99): SAT {fs99:.3f}  CTL {fc99:.3f}")
    fsd = sum(r['dstar'] <= 4 for _, r in all_sat) / max(1, len(all_sat))
    fcd = sum(r['dstar'] <= 4 for _, r in all_ctl) / max(1, len(all_ctl))
    print(f"  worst coset 2-adically near mu_n (d*<=4, b* in mu_4n): "
          f"SAT {fsd:.3f}  CTL {fcd:.3f}")

    print("\n  matched pairs (same n, nearest size => matched beta):")
    ratios = []
    for n, r, rq in pairs:
        ratios.append(r['C'] / rq['C'])
        print(f"    n={n:>2d} p_sat={r['p']:>11d} C={r['C']:.4f} | "
              f"p_ctl={rq['p']:>11d} C={rq['C']:.4f} | "
              f"C_sat/C_ctl={ratios[-1]:.4f} | "
              f"pct0 {r['pct0']:.3f} vs {rq['pct0']:.3f}")
    ratios = np.array(ratios)
    print(f"  C inflation: mean ratio {ratios.mean():.4f}, "
          f"median {np.median(ratios):.4f}, frac>1 {np.mean(ratios > 1):.3f}, "
          f"frac>=1.15 {np.mean(ratios >= 1.15):.3f}")

    # ---------------- decision ----------------
    print("\nDECISION")
    loc_real = fs >= 0.70 and fc < 0.20
    infl_real = ratios.mean() >= 1.15 and np.mean(ratios > 1) >= 0.70
    if loc_real or infl_real:
        why = []
        if loc_real:
            why.append(f"mu_n-selection SAT {fs:.2f} >= 0.70 vs CTL {fc:.2f} < 0.20")
        if infl_real:
            why.append(f"C inflation mean {ratios.mean():.2f} >= 1.15 at matched beta")
        print("  FAMILY-REAL: " + "; ".join(why))
    else:
        print(f"  FAMILY-ARTIFACT by the lane thresholds: mu_n-selection SAT {fs:.2f}"
              f" (need >=0.70) vs CTL {fc:.2f}; C ratio mean {ratios.mean():.3f}"
              f" (need >=1.15).")
        if fs99 >= 0.7 and fc99 < 0.2:
            print(f"  BUT note relaxed location signal: mu_n coset in top-1% for"
                  f" SAT {fs99:.2f} vs CTL {fc99:.2f} -- report as partial.")

    print()
    gf_phase2()
    print(f"\ntotal wall time {time.time()-t_all:.1f}s")


if __name__ == "__main__":
    main()
