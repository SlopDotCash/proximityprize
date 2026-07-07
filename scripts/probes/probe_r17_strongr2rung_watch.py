#!/usr/bin/env python3
"""R17 WATCH lane: StrongR2Rung falsification watch pushed to n=64 (and n=128 where feasible),
plus dense n=32 rescan around the thin-margin cell (n=32, deg=4, p=12289).

Quantities per cell (p, n, deg), H = index-deg subgroup containing mu_n, D = {0} u mu_n:
  eta_b   = sum_{x in mu_n} e_p(b x)            (one length-p FFT)
  I_H(s0) = sum_{b in H} conj(eta_b) e_p(b s0)  (second length-p FFT)
  Sigma   = sum_{b in H} |eta_b|^2 ; quart = sum_{b in H}|eta_b|^4
  S2_full = sum_{s0} |I|^4 ; spike = sum_{s0 in D} |I|^4 ; S2_away = S2_full - spike
  Wick    = 3 q Sigma^2 (q = p)
  StrongR2Rung bound: S2_away <= 2 q Sigma^2 ; margin = 1 - S2_away/(2 q Sigma^2)
  b-space: q*Q_all = S2_full exactly, Q_pair = 2 Sigma^2 - quart, Off = Q_all - Q_pair
  residual = (q*Off - spike)/Wick   [StrongR2Rung <=> q*Off - spike <= q*quart]
"""
import math, sys, time
import numpy as np
from scipy import fft as sfft


def is_prime(n):
    if n < 2: return False
    for d in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        if n % d == 0: return n == d
    d, r = n - 1, 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True


def factor(x):
    fs, d = set(), 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs


def prim_root(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError


def cell(p, n, deg):
    if (p - 1) % n or (p - 1) % deg or (n * deg) > (p - 1):
        return None
    # mu_n <= H iff deg | (p-1)/n
    if ((p - 1) // n) % deg:
        return None
    t0 = time.time()
    g = prim_root(p)
    gm = pow(g, (p - 1) // n, p)
    mun = []
    x = 1
    for _ in range(n):
        mun.append(x); x = x * gm % p
    gd = pow(g, deg, p)
    m = (p - 1) // deg
    H = np.empty(m, dtype=np.int64)
    x = 1
    for i in range(m):
        H[i] = x; x = x * gd % p

    ind = np.zeros(p, dtype=np.float64)
    ind[np.array(mun)] = 1.0
    eta = sfft.fft(ind).conj()  # eta_b = sum_x e^{+2pi i b x/p} = conj(fft(ind))[b]
    del ind
    etaH = eta[H]
    del eta
    Sigma = float(np.sum(np.abs(etaH) ** 2))
    quart = float(np.sum(np.abs(etaH) ** 4))
    w = np.zeros(p, dtype=np.complex128)
    w[H] = etaH.conj()
    # I(s0) = sum_b w_b e^{+2pi i b s0/p} = p * ifft(w)
    I = sfft.ifft(w, overwrite_x=True) * p
    absI4 = np.abs(I) ** 2
    del I, w
    absI4 *= absI4
    S2_full = float(np.sum(absI4))
    Dset = np.array([0] + mun)
    spike = float(np.sum(absI4[Dset]))
    del absI4
    S2_away = S2_full - spike
    q = float(p)
    Wick = 3 * q * Sigma * Sigma
    strong = 2 * q * Sigma * Sigma
    margin = 1 - S2_away / strong
    Q_all = S2_full / q
    Off = Q_all - (2 * Sigma * Sigma - quart)
    residual = (q * Off - spike) / Wick
    beta = math.log(p) / math.log(n)
    return dict(p=p, n=n, deg=deg, beta=beta, Sigma=Sigma,
                ratio_strong=S2_away / strong, ratio_wick=S2_away / Wick,
                margin=margin, residual=residual, spike_over_wick=spike / Wick,
                t=time.time() - t0)


def primes_1mod(n, lo, hi, count):
    out = []
    p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while p <= hi and len(out) < count:
        if is_prime(p): out.append(p)
        p += n
    return out


def report(r):
    viol = " *** VIOLATION ***" if r['ratio_strong'] > 1 else ""
    print(f"n={r['n']:4d} deg={r['deg']:3d} p={r['p']:9d} beta={r['beta']:.3f} "
          f"S2'/2qS^2={r['ratio_strong']:.5f} margin={r['margin']:+.5f} "
          f"S2'/Wick={r['ratio_wick']:.5f} resid={r['residual']:+.5f} "
          f"spike/W={r['spike_over_wick']:.3f} [{r['t']:.1f}s]{viol}", flush=True)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    results = []
    if mode in ("n32", "all"):
        print("=== n=32 dense rescan, beta in [2.5,4.4], deg 2/4/8 ===")
        n = 32
        # spread primes across beta range
        betas = [2.6, 2.7, 2.8, 2.9, 3.0, 3.2, 3.4, 3.6, 3.8, 4.0, 4.2, 4.4]
        ps = sorted(set(sum([primes_1mod(n, int(n**b), int(n**b * 1.5), 2) for b in betas], [])))
        ps = sorted(set(ps + [12289]))
        for p in ps:
            for deg in (2, 4, 8):
                r = cell(p, n, deg)
                if r: results.append(r); report(r)
    if mode in ("n64", "all"):
        print("=== n=64, deg 2/4, beta 3 / 3.5 / 4 windows ===")
        n = 64
        ps = []
        for lo in (int(n**3), int(n**3.5), int(n**4)):
            ps += primes_1mod(n, lo, int(lo * 1.3), 2)
        for p in sorted(set(ps)):
            for deg in (2, 4):
                r = cell(p, n, deg)
                if r: results.append(r); report(r)
    if mode in ("n128", "all"):
        print("=== n=128, deg 2/4, beta 3 / ~3.4 ===")
        n = 128
        ps = primes_1mod(n, int(n**3), int(n**3 * 1.3), 2) + \
             primes_1mod(n, int(n**3.4), int(n**3.4 * 1.2), 1)
        for p in sorted(set(ps)):
            for deg in (2, 4):
                r = cell(p, n, deg)
                if r: results.append(r); report(r)
    if results:
        worst = min(results, key=lambda r: r['margin'])
        print("\nMIN MARGIN:")
        report(worst)
        v = [r for r in results if r['ratio_strong'] > 1]
        print(f"VIOLATIONS: {len(v)}")


if __name__ == "__main__":
    main()
