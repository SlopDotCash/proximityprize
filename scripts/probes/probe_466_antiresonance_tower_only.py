#!/usr/bin/env python3
"""probe_466_antiresonance_tower_only.py

Q3 companion to probe_466_antiresonance_tower_worstb.py: the thin-dyadic TOWER
recursion of the WORST-B quarter-arc energy A2q*, computed on moderate high-2-adic
primes so every level stays thin (p >= n^4) AND m = (p-1)/n stays tractable. For
large m the worst-b is found by a bounded coset SAMPLE (sound lower bound on M and
on A2q*; the tower ratio is read off the same sampled worst coset each level, so the
ratio is an apples-to-apples estimate of the deterministic tower map).

Question: is A2q*(mu_{2n})/A2q*(mu_n) a sub-doubling contraction (< 2 - eps, a spectral
gap => a live descent lever) or ~ 2 (deterministic factor-2 relabel => KILL, matching
the wf-F4 dyadic-descent refutation)?
"""

import sys
import math
import numpy as np

_MR = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_prime(n):
    if n < 2:
        return False
    for p in _MR:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR:
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


def factorize(n):
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


def primitive_root(p):
    fac = list(factorize(p - 1).keys())
    g = 2
    while True:
        if all(pow(g, (p - 1) // r, p) != 1 for r in fac):
            return g
        g += 1


CHUNK = 4096
MAX_COSETS = 200000  # cap the worst-b scan; sample if m larger (sound lower bound)


def worstb_and_a2q(n, p, rng):
    m = (p - 1) // n
    g = primitive_root(p)
    h = pow(g, m, p)
    X = np.empty(n, dtype=np.int64)
    x = 1
    for k in range(n):
        X[k] = x
        x = x * h % p
    if m <= MAX_COSETS:
        reps = np.arange(m, dtype=np.int64)
        Bvals = np.empty(m, dtype=np.int64)
        b = 1
        for j in range(m):
            Bvals[j] = b
            b = b * g % p
        sampled = False
    else:
        # sample MAX_COSETS distinct exponents -> b = g^e (sound lower bound on M)
        exps = rng.choice(m, size=MAX_COSETS, replace=False)
        Bvals = np.array([pow(g, int(e), p) for e in exps], dtype=np.int64)
        sampled = True
    mm = len(Bvals)
    abs_eta = np.empty(mm)
    for lo in range(0, mm, CHUNK):
        hi = min(lo + CHUNK, mm)
        E = (Bvals[lo:hi, None] * X[None, :]) % p
        z = np.exp(2j * np.pi * (E.astype(np.float64) / p)).sum(axis=1)
        abs_eta[lo:hi] = np.abs(z)
    jstar = int(np.argmax(abs_eta))
    M = float(abs_eta[jstar])
    bstar = int(Bvals[jstar])
    T = np.sort(((bstar * X) % p).astype(np.float64) / p)
    D = np.abs(T[:, None] - T[None, :])
    D = np.minimum(D, 1.0 - D)
    iu = np.triu_indices(n, 1)
    Dp = D[iu]
    A2q = float(np.maximum(0.0, 1.0 - Dp / 0.25).sum() / n)
    R = M / math.sqrt(n * A2q) if A2q > 1e-12 else float("nan")
    logf = math.log(p / n)
    return dict(m=m, M=M, C=M / math.sqrt(n * logf), A2q=A2q, R=R, sampled=sampled)


def main():
    print("probe_466_antiresonance_tower_only")
    print(f"numpy {np.__version__}; worst-b (full if m<=200k else sampled lower bound)")
    print("=" * 80)
    rng = np.random.default_rng(4661122)
    # moderate high-2-adic primes: thin low levels + tractable m
    cands = [40961, 65537, 786433, 5767169, 7340033, 23068673, 104857601, 167772161]
    tower_primes = [c for c in cands if is_prime(c)]
    all_ratios = []
    for p in tower_primes:
        v2 = ((p - 1) & -(p - 1)).bit_length() - 1
        t_hi = min(v2 - 1, int(math.log2(p) / 4))
        t_lo = 3
        if t_hi < t_lo + 1:
            continue
        print(f"\n  p={p} (v2={v2}, thin tower t={t_lo}..{t_hi})")
        print(f"    {'t':>3} {'n':>5} {'m':>10} {'M':>9} {'C':>7} {'A2q*':>8} "
              f"{'R(b*)':>7} {'A2q*_up/prev':>12} {'samp':>5}")
        prev = None
        for t in range(t_lo, t_hi + 1):
            n = 1 << t
            if (p - 1) % n != 0 or n * n >= p:
                continue
            r = worstb_and_a2q(n, p, rng)
            ratio = (r["A2q"] / prev) if prev is not None else float("nan")
            print(f"    {t:>3} {n:>5} {r['m']:>10} {r['M']:>9.3f} {r['C']:>7.4f} "
                  f"{r['A2q']:>8.4f} {r['R']:>7.4f} {ratio:>12.4f} {str(r['sampled']):>5}")
            if ratio == ratio:
                all_ratios.append(ratio)
            prev = r["A2q"]
            sys.stdout.flush()
    print("\n" + "=" * 80)
    if all_ratios:
        tr = np.array(all_ratios)
        print(f"Q3 tower A2q* ratio up: mean={tr.mean():.3f} min={tr.min():.3f} "
              f"max={tr.max():.3f} median={np.median(tr):.3f} (n={len(tr)})")
        print(f"   spectral-gap contraction (< 1.85)? {tr.mean() < 1.85}")
        print("   deterministic factor-2 relabel if ratio ~ 2 (KILL, matches wf-F4).")
    else:
        print("   (no usable thin-tower levels)")


if __name__ == "__main__":
    main()
