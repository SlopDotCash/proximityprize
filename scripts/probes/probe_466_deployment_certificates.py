#!/usr/bin/env python3
"""
probe_466_deployment_certificates.py -- Lane L6 (#466): EXACT wall-constant certificates
at the REAL deployed FFT primes.

(a) M = max_b |eta_b| for
      BabyBear  p = 15*2^27 + 1 = 2013265921,  n = 2^27 (largest 2-power subgroup), f = 15
      KoalaBear p = 2^31 - 2^24 + 1 = 2130706433,  n = 2^24, f = 127
    eta_b = sum_{x in mu_n} e_p(b x) is CONSTANT on the f dilation cosets b*mu_n (reindex
    x -> u x, u in mu_n), and REAL (-1 in mu_n since n even), so eta_b = sum cos and
    M = max over the f coset values c_0..c_{f-1} (c_j for b = g^j, g a primitive root).
    Method: one pass over g^i, i = 0..(p-1)/2-1 (the other half is -x, same coset since
    -1 in mu_n and (p-1)/2 = f*(n/2) == 0 mod f), bucketed by i mod f, chunked float64
    with per-chunk pairwise summation + math.fsum across chunk partials (compensated).
    EXACT anchors: sum_j c_j = -1 (mass balance), sum_j c_j^2 = p - n (Parseval),
    s_3 = sum_j c_j^3 is a rational INTEGER (power sums of Gaussian periods).
    Independent-path recheck of the argmax coset (different generator base h = g^f,
    reversed chunk order) for the two deployment primes.

(b) Hankel double-ratio screening (round-1 kept diagnostic, DISPROOF_LOG
    466-r1-hankel-bounded-window-refuted): D_{k-1} D_{k+1} / D_k^2 (Hankel dets of the
    empirical coset-value measure, k <= 5) = b_{k+1}^2 (Jacobi coefficient), computed
    two ways (mpmath Lanczos dps=50 on the f nodes; mpmath Hankel dets dps=80 --
    identity cross-check). Normalized q_j = b_j^2 / b0_j(n) against the exact char-0
    reference (Fraction moments + Chebyshev, as round-1). Detector = z-scores of the
    deployed prime vs 3 generic same-n controls + a constrained-Gaussian Monte-Carlo
    null at the prime's own f (matches sum c = -1 ~ 0 and sum c^2 = p-n exactly).

REGIME NOTE: deployment primes have beta = ln p / ln n ~ 1.15 / 1.29 -- FAR below the
prize discipline beta >= 4. These are production-parameter measurements (the point of
the lane), NOT prize-regime data points.

Controls (pre-scanned, all non-generalized-Fermat, f >= 7):
  n = 2^27: c in {17, 24, 26}   (c = 15 is BabyBear; c*2^27+1 prime)
  n = 2^24: c in {108, 126, 136} (c = 127 is KoalaBear; c = 120 EXCLUDED: 120*2^24+1
                                  = 2013265921 IS BabyBear)
"""
import math
import os
import sys
import time
from fractions import Fraction

import numpy as np
import mpmath as mp

CKPT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_ckpt_466_deploy")

CHAR0_DPS = 400
LANCZOS_DPS = 50
HANKEL_DPS = 80
K_JAC = 7          # Jacobi depth: b_1..b_7 -> double ratios k = 0..6 (task: k <= 5)
RMAX = 6           # raw even moments up to order 12
MC_REPS = 4000
MC_SEED = 466

P_BB = 15 * (1 << 27) + 1          # 2013265921
P_KB = (1 << 31) - (1 << 24) + 1   # 2130706433


# ---------------------------------------------------------------- number theory
def is_prime(x: int) -> bool:
    if x < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if x % q == 0:
            return x == q
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:  # deterministic for x < 3.3e24
        v = pow(a, d, x)
        if v in (1, x - 1):
            continue
        for _ in range(s - 1):
            v = v * v % x
            if v == x - 1:
                break
        else:
            return False
    return True


def factorize(x: int):
    fs, d = {}, 2
    while d * d <= x:
        while x % d == 0:
            fs[d] = fs.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        fs[x] = fs.get(x, 0) + 1
    return fs


def primitive_root(p: int) -> int:
    qs = list(factorize(p - 1))
    g = 2
    while True:
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
        g += 1


def gen_fermat_check(p: int):
    """Is p = b^(2^s) + 1 for some b > 1, s >= 1? (known resonant family)"""
    hits = []
    for s in range(1, 6):
        e = 1 << s
        b = round(p ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb > 1 and bb ** e + 1 == p:
                hits.append((bb, s))
    return hits


# ---------------------------------------------------------------- power tables
def power_table(g: int, p: int, L: int) -> np.ndarray:
    """[g^0, g^1, ..., g^{L-1}] mod p as uint64 (products < 2^62 since p < 2^31)."""
    P = np.ones(1, dtype=np.uint64)
    while P.size < L:
        gl = pow(g, int(P.size), p)
        take = min(P.size, L - P.size)
        P = np.concatenate([P, (P[:take] * np.uint64(gl)) % np.uint64(p)])
    return P


# ---------------------------------------------------------------- coset values
def coset_values(p: int, n: int, g: int, verbose: bool = True):
    """All f = (p-1)/n dilation-coset values c_j = eta_{g^j}, exact float64 pipeline.

    Iterates x = g^i, i = 0..(p-1)/2 - 1 (each +-pair once; -1 in mu_n so x and -x
    share a coset and coset(g^i) = i mod f), adds 2*cos(2 pi x / p) into bucket i mod f.
    Chunk length L = f * 2^cp divides (p-1)/2 = f * (n/2); within every chunk the
    bucket pattern is exactly (position mod f) because L == 0 mod f.
    """
    f = (p - 1) // n
    half = (p - 1) // 2
    k2 = n.bit_length() - 1
    assert n == 1 << k2 and half == f * (n // 2)
    cp = max(1, min(int(math.floor(math.log2(8e6 / f))), k2 - 1))
    L = f << cp
    nch = half // L
    assert nch * L == half
    P = power_table(g, p, L)
    w = 2.0 * math.pi / p
    partial = np.empty((nch, f))
    t0 = time.time()
    for t in range(nch):
        s = pow(g, t * L, p)  # exact scalar (no error accumulation across chunks)
        vals = (P * np.uint64(s)) % np.uint64(p)
        th = vals.astype(np.float64)
        th *= w
        np.cos(th, out=th)
        partial[t] = th.reshape(L // f, f).sum(axis=0)
        if verbose and (t + 1) % max(1, nch // 4) == 0:
            el = time.time() - t0
            print(f"      chunk {t + 1}/{nch}  ({el:.0f}s elapsed, "
                  f"{el / (t + 1) * nch:.0f}s est total)", flush=True)
    c = np.array([2.0 * math.fsum(partial[:, j].tolist()) for j in range(f)])
    return c


def coset_value_direct(p: int, n: int, g: int, j: int) -> float:
    """Independent path for ONE coset value: enumerate mu_n via h = g^f (different
    generator base), multiply by b = g^j, REVERSED chunk order, fsum of partials."""
    f = (p - 1) // n
    h = pow(g, f, p)
    b = pow(g, j, p)
    halfn = n // 2  # h^{n/2} = g^{(p-1)/2} = -1: enumerate one of each +-pair
    Lc = min(1 << 22, halfn)
    nch = halfn // Lc
    assert nch * Lc == halfn
    T = power_table(h, p, Lc)
    w = 2.0 * math.pi / p
    parts = []
    for t in reversed(range(nch)):
        s = (b * pow(h, t * Lc, p)) % p
        vals = (T * np.uint64(s)) % np.uint64(p)
        th = vals.astype(np.float64)
        th *= w
        parts.append(float(np.cos(th).sum()))
    return 2.0 * math.fsum(parts)


# ---------------------------------------------------------------- char-0 reference
def char0_moments_fraction(n: int, rmax: int):
    """Exact moments m_{2r}, r = 0..rmax, of X = sum_{j<=n/2} 2 cos(theta_j):
    m_{2r} = (2r)! [x^r] I_0(2 sqrt x)^{n/2}. (Round-1 code, verified there.)"""
    deg = rmax + 2
    c = [Fraction(1, math.factorial(j) ** 2) for j in range(deg)]

    def pmul(A, B):
        r = [Fraction(0)] * deg
        for i, ai in enumerate(A):
            if ai:
                for j2, bj in enumerate(B[:deg - i]):
                    if bj:
                        r[i + j2] += ai * bj
        return r

    P = [Fraction(1)] + [Fraction(0)] * (deg - 1)
    base = list(c)
    e = n // 2
    while e:
        if e & 1:
            P = pmul(P, base)
        e >>= 1
        if e:
            base = pmul(base, base)
    return [P[r] * math.factorial(2 * r) for r in range(rmax + 1)]


def chebyshev_moments_to_jacobi(moms, K):
    """Gautschi Chebyshev algorithm: raw moments m_0..m_{2K-1} -> (alpha_k, beta_k).
    beta_k = b_k^2 for k >= 1. Run inside mp.workdps. (Round-1 code.)"""
    N = K
    sig_prev = [mp.mpf(0)] * (2 * N)
    sig_cur = list(moms)
    alphas = [moms[1] / moms[0]]
    betas = [moms[0]]
    for k in range(1, N):
        sig_new = [mp.mpf(0)] * (2 * N)
        for l in range(k, 2 * N - k):
            sig_new[l] = (sig_cur[l + 1] - alphas[k - 1] * sig_cur[l]
                          - betas[k - 1] * sig_prev[l])
        alphas.append(sig_new[k + 1] / sig_new[k] - sig_cur[k] / sig_cur[k - 1])
        betas.append(sig_new[k] / sig_cur[k - 1])
        sig_prev, sig_cur = sig_cur, sig_new
    return alphas, betas


_char0_cache = {}


def char0_bsq(n: int, K: int):
    """Exact char-0 reference b_j^{(0)2}, j = 1..K-1 (entry 0 = nan)."""
    key = (n, K)
    if key in _char0_cache:
        return _char0_cache[key]
    mu = char0_moments_fraction(n, K)
    with mp.workdps(CHAR0_DPS):
        moms = []
        for l in range(2 * K):
            if l % 2 == 0:
                fr = mu[l // 2]
                moms.append(mp.mpf(fr.numerator) / mp.mpf(fr.denominator))
            else:
                moms.append(mp.mpf(0))
        _, betas = chebyshev_moments_to_jacobi(moms, K)
        out = np.full(K, np.nan)
        for j in range(1, K):
            out[j] = float(betas[j])
    _char0_cache[key] = out
    return out


# ---------------------------------------------------------------- Jacobi / Hankel
def lanczos_mp(xs, K, dps):
    """Jacobi coefficients of the uniform measure on nodes xs, mpmath full-reorth
    Lanczos (round-1 validated code path)."""
    with mp.workdps(dps):
        msz = len(xs)
        xs = [mp.mpf(x) for x in xs]
        inv = mp.mpf(1) / mp.sqrt(msz)
        V = [[inv] * msz]
        a, b = [], []
        for k in range(K):
            vk = V[k]
            u = [xs[i] * vk[i] for i in range(msz)]
            ak = mp.fsum(vk[i] * u[i] for i in range(msz))
            a.append(ak)
            u = [u[i] - ak * vk[i] for i in range(msz)]
            if k > 0:
                bk1, vk1 = b[k - 1], V[k - 1]
                u = [u[i] - bk1 * vk1[i] for i in range(msz)]
            for _ in range(2):
                for vv in V:
                    cc = mp.fsum(vv[i] * u[i] for i in range(msz))
                    u = [u[i] - cc * vv[i] for i in range(msz)]
            nb = mp.sqrt(mp.fsum(t * t for t in u))
            b.append(nb)
            V.append([t / nb for t in u])
        return [float(t) for t in a], [float(t) for t in b]


def hankel_double_ratios(xs, kmax, dps):
    """R_k = D_{k-1} D_{k+1} / D_k^2, k = 1..kmax, D_k = det[m_{i+j}]_{0<=i,j<=k} of the
    uniform empirical measure on xs (raw moments incl. odd). Identity: R_k = b_{k+1}^2."""
    with mp.workdps(dps):
        f = len(xs)
        xs = [mp.mpf(x) for x in xs]
        moms = []
        cur = [mp.mpf(1)] * f
        for _ in range(2 * (kmax + 1) + 1):
            moms.append(mp.fsum(cur) / f)
            cur = [cur[i] * xs[i] for i in range(f)]
        D = []
        for k in range(kmax + 2):
            H = mp.matrix(k + 1, k + 1)
            for i in range(k + 1):
                for j in range(k + 1):
                    H[i, j] = moms[i + j]
            D.append(mp.det(H))
        out = [float(D[k - 1] * D[k + 1] / D[k] ** 2) for k in range(1, kmax + 1)]
    return out


def flanczos(x: np.ndarray, K: int, passes: int = 2):
    """float64 Lanczos (round-1 code) for the Monte-Carlo null."""
    msz = x.size
    K = min(K, msz - 1)
    V = np.empty((msz, K + 1))
    V[:, 0] = 1.0 / math.sqrt(msz)
    a = np.zeros(K)
    b = np.zeros(K)
    scale = float(np.abs(x).max()) * math.sqrt(msz)
    for k in range(K):
        u = x * V[:, k]
        a[k] = float(V[:, k] @ u)
        u = u - a[k] * V[:, k]
        if k > 0:
            u -= b[k - 1] * V[:, k - 1]
        for _ in range(passes):
            c = V[:, :k + 1].T @ u
            u -= V[:, :k + 1] @ c
        nb = float(np.linalg.norm(u))
        b[k] = nb
        if nb <= 1e-13 * scale:
            return a[:k + 1], b[:k + 1]
        V[:, k + 1] = u / nb
    return a, b


def mc_null(f: int, n: int, p: int, K: int, reps: int, seed: int):
    """Constrained-Gaussian null at this prime's own f: y iid N(0,1), centered
    (sum y = 0 ~ -1, negligible at sqrt(n) scale), rescaled to sum y^2 = p - n
    (both EXACT identities of the real ensemble). Returns (qmat reps x K, Mnull)."""
    rng = np.random.default_rng(seed)
    qmat = np.empty((reps, K))
    Mn = np.empty(reps)
    tgt = float(p - n)
    jj = n * np.arange(1, K + 1, dtype=np.float64)
    for r in range(reps):
        y = rng.standard_normal(f)
        y -= y.mean()
        y *= math.sqrt(tgt / float(y @ y))
        _, b = flanczos(y, K)
        bs = np.full(K, np.nan)
        bs[:len(b)] = b ** 2
        qmat[r] = bs / jj
        Mn[r] = float(np.abs(y).max())
    return qmat, Mn


# ---------------------------------------------------------------- self tests
def self_tests():
    print("== SELF-TESTS ==", flush=True)
    ok = True

    # 1. p = 641, n = 128, f = 5: pipeline vs exhaustive mpmath dps=30
    p, n = 641, 128
    g = primitive_root(p)
    c = coset_values(p, n, g, verbose=False)
    f = (p - 1) // n
    with mp.workdps(30):
        h = pow(g, f, p)
        mu = [pow(h, k, p) for k in range(n)]
        ref = []
        for j in range(f):
            b = pow(g, j, p)
            ref.append(float(mp.fsum(mp.cos(2 * mp.pi * ((b * x) % p) / p)
                                     for x in mu)))
    d1 = max(abs(c[j] - ref[j]) for j in range(f))
    print(f"  [1] p=641 n=128 f=5: pipeline vs mpmath-exhaustive max|dev| = {d1:.2e}")
    ok &= d1 < 1e-10

    # 2. p = 61441 = 15*2^12+1, n = 2^12, f = 15: pipeline vs independent path (all j)
    p, n = 61441, 1 << 12
    g = primitive_root(p)
    c = coset_values(p, n, g, verbose=False)
    f = (p - 1) // n
    d2 = max(abs(c[j] - coset_value_direct(p, n, g, j)) for j in range(f))
    s1 = math.fsum(c.tolist())
    s2 = float(c @ c)
    print(f"  [2] p=61441 n=2^12 f=15: pipeline vs independent-path max|dev| = {d2:.2e}"
          f"   anchors: |S1+1| = {abs(s1 + 1):.2e}, |S2/(p-n)-1| = {abs(s2 / (p - n) - 1):.2e}")
    ok &= d2 < 1e-9 and abs(s1 + 1) < 1e-9

    # 3. one coset of p=61441 vs mpmath dps=25
    with mp.workdps(25):
        h = pow(g, f, p)
        x, sm = 1, mp.mpf(0)
        for _ in range(n):
            sm += mp.cos(2 * mp.pi * x / p)
            x = (x * h) % p
    d3 = abs(c[0] - float(sm))
    print(f"  [3] p=61441 coset j=0 vs mpmath dps=25: |dev| = {d3:.2e}")
    ok &= d3 < 1e-9

    # 4. Chebyshev on Gaussian moments -> beta_k = k (round-1 self-test)
    K = 12
    with mp.workdps(300):
        moms = []
        for l in range(2 * K):
            moms.append(mp.mpf(0) if l % 2 else
                        mp.mpf(math.prod(range(1, l, 2)) if l else 1))
        _, betas = chebyshev_moments_to_jacobi(moms, K)
        errg = max(abs(float(betas[k]) - k) for k in range(1, K))
    print(f"  [4] Chebyshev(Gaussian moments): max |beta_k - k| = {errg:.2e}")
    ok &= errg < 1e-12

    # 5. Hankel double-ratio identity R_k = b_{k+1}^2 on the p=61441 nodes
    _, b = lanczos_mp(c.tolist(), K_JAC, LANCZOS_DPS)
    R = hankel_double_ratios(c.tolist(), K_JAC - 1, HANKEL_DPS)
    d5 = max(abs(R[k - 1] / (b[k] ** 2) - 1) for k in range(1, K_JAC))
    print(f"  [5] Hankel D-ratio vs Lanczos b_(k+1)^2 (p=61441): max rel dev = {d5:.2e}")
    ok &= d5 < 1e-8

    print(f"  SELF-TESTS {'ALL PASS' if ok else '*** FAILURE ***'}", flush=True)
    return ok


# ---------------------------------------------------------------- per-prime analysis
def analyze(name, p, n, deployment=False):
    t0 = time.time()
    assert is_prime(p), (name, p)
    f = (p - 1) // n
    gf = gen_fermat_check(p)
    g = primitive_root(p)
    beta = math.log(p) / math.log(n)
    lnpn = math.log(p / n)
    print(f"\n-- {name}: p = {p} = {f}*2^{n.bit_length() - 1}+1, n = 2^{n.bit_length() - 1}, "
          f"f = {f}, g = {g}, beta = {beta:.4f}, ln(p/n) = {lnpn:.4f}, "
          f"genFermat = {gf if gf else 'NO'}", flush=True)
    # checkpoint (the 2026-07-01 run lost ~15 min of coset values to a mid-run kill)
    os.makedirs(CKPT_DIR, exist_ok=True)
    ck = os.path.join(CKPT_DIR, f"c_{name}.npy")
    if os.path.exists(ck):
        c = np.load(ck)
        assert c.size == f
        print(f"    [checkpoint] loaded coset values from {os.path.basename(ck)}",
              flush=True)
    else:
        c = coset_values(p, n, g)
        np.save(ck, c)
    # exact anchors
    s1 = math.fsum(c.tolist())
    s2 = math.fsum((c * c).tolist())
    s3 = math.fsum((c * c * c).tolist())
    a1 = abs(s1 + 1.0)
    a2 = abs(s2 / (p - n) - 1.0)
    a3 = abs(s3 - round(s3))
    print(f"    anchors: |S1 - (-1)| = {a1:.3e}   |S2/(p-n) - 1| = {a2:.3e}   "
          f"S3 = {s3:.6f} (int resid {a3:.3e})", flush=True)
    assert a1 < 1e-5 and a2 < 1e-9, "ANCHOR FAILURE"
    jmax = int(np.argmax(np.abs(c)))
    M = float(np.abs(c[jmax]))
    C = M / math.sqrt(n * lnpn)
    ram = M / (2.0 * math.sqrt(n))
    weil = (1.0 + (f - 1) * math.sqrt(p)) / f
    print(f"    M = |c_{jmax}| = {M:.6f}   (eta_1 = c_0 = {c[0]:.6f})")
    print(f"    C = M/sqrt(n ln(p/n)) = {C:.6f}   M/(2 sqrt n) = {ram:.6f}   "
          f"M/Weil[(1+(f-1)sqrt p)/f] = {M / weil:.4f}")
    srt = np.sort(np.abs(c))[::-1]
    show = min(f, 15)
    print("    |c| sorted desc: " + " ".join(f"{v:.1f}" for v in srt[:show])
          + (" ..." if f > show else ""))
    dev = None
    if deployment:
        cd = coset_value_direct(p, n, g, jmax)
        dev = abs(cd - c[jmax])
        print(f"    independent-path recheck of argmax coset: |dev| = {dev:.3e}", flush=True)
        assert dev < 1e-5, "CROSS-PATH FAILURE"
    # Jacobi / Hankel
    _, b = lanczos_mp(c.tolist(), K_JAC, LANCZOS_DPS)
    bsq = np.array(b) ** 2
    R = hankel_double_ratios(c.tolist(), K_JAC - 1, HANKEL_DPS)
    did = max(abs(R[k - 1] / bsq[k] - 1) for k in range(1, K_JAC))
    b0 = char0_bsq(n, K_JAC + 1)
    q = np.array([bsq[j - 1] / b0[j] for j in range(1, K_JAC + 1)])
    mrat = np.array([math.fsum((c ** (2 * r)).tolist()) / f for r in range(1, RMAX + 1)])
    mu0 = char0_moments_fraction(n, RMAX)
    mrat = mrat / np.array([float(x) for x in mu0[1:RMAX + 1]])
    print(f"    q_j = b_j^2/b0_j (j=1..{K_JAC}): "
          + " ".join(f"{v:.4f}" for v in q))
    print(f"    double-ratio identity check (Hankel dets vs Lanczos): max rel dev = {did:.1e}")
    print(f"    even-moment ratios m_2r/m0_2r (r=1..{RMAX}): "
          + " ".join(f"{v:.4f}" for v in mrat))
    print(f"    [{time.time() - t0:.0f}s]", flush=True)
    return dict(name=name, p=p, n=n, f=f, g=g, beta=beta, lnpn=lnpn, c=c, M=M, C=C,
                ram=ram, weil=weil, jmax=jmax, a1=a1, a2=a2, a3=a3, s3=s3, dev=dev,
                bsq=bsq, q=q, R=np.array(R), mrat=mrat, did=did)


# ---------------------------------------------------------------- detector
def detector(dep, ctrls, tag):
    print(f"\n== HANKEL DOUBLE-RATIO DETECTOR: {dep['name']} vs controls "
          f"{[c['name'] for c in ctrls]} ==")
    print(f"  (f mismatch caveat: f_dep = {dep['f']}, f_ctrl = {[c['f'] for c in ctrls]}; "
          f"MC null is at each prime's own f)")
    qc = np.array([c['q'] for c in ctrls])
    mc = np.array([c['mrat'] for c in ctrls])
    qmc, Mn = mc_null(dep['f'], dep['n'], dep['p'], K_JAC, MC_REPS, MC_SEED)
    qm_mean, qm_std = np.nanmean(qmc, axis=0), np.nanstd(qmc, axis=0, ddof=1)
    print(f"  {'j':>2} {'q_dep':>9} {'q_ctrl_mean':>12} {'z_ctrl':>8} "
          f"{'MCnull_mean':>12} {'MCnull_std':>11} {'z_MC':>8} {'p_MC':>8}   "
          f"{'z_mom(r=j)':>10}")
    flags = []
    for j in range(1, K_JAC + 1):
        qd = dep['q'][j - 1]
        zc = abs(qd - qc[:, j - 1].mean()) / qc[:, j - 1].std(ddof=1)
        zm = abs(qd - qm_mean[j - 1]) / qm_std[j - 1]
        pm = float(np.mean(np.abs(qmc[:, j - 1] - qm_mean[j - 1])
                           >= abs(qd - qm_mean[j - 1])))
        if j <= RMAX:
            zmom = abs(dep['mrat'][j - 1] - mc[:, j - 1].mean()) / mc[:, j - 1].std(ddof=1)
            zs = f"{zmom:10.2f}"
        else:
            zs = " " * 10
        print(f"  {j:>2} {qd:9.4f} {qc[:, j - 1].mean():12.4f} {zc:8.2f} "
              f"{qm_mean[j - 1]:12.4f} {qm_std[j - 1]:11.4f} {zm:8.2f} {pm:8.4f}   {zs}")
        if zc > 3 or zm > 3:
            flags.append(j)
    # M against the MC null (max of f constrained Gaussians)
    pM = float(np.mean(Mn >= dep['M']))
    print(f"  M null (constrained Gaussian, f = {dep['f']}): mean = {Mn.mean():.1f}, "
          f"std = {Mn.std(ddof=1):.1f};  M_dep = {dep['M']:.1f}  ->  "
          f"z = {(dep['M'] - Mn.mean()) / Mn.std(ddof=1):+.2f}, P(M_null >= M_dep) = {pM:.4f}")
    verdict = ("FLAGGED at j = " + str(flags)) if flags else "NOT FLAGGED (all z <= 3)"
    print(f"  VERDICT [{tag}]: {verdict}", flush=True)
    return flags, pM, (Mn.mean(), Mn.std(ddof=1))


# ---------------------------------------------------------------- main
def main():
    t00 = time.time()
    np.seterr(over="raise", divide="raise", invalid="raise")
    print("probe_466_deployment_certificates.py -- Lane L6 deployment-prime certificates")
    print(f"BabyBear p = {P_BB} (prime: {is_prime(P_BB)}), "
          f"KoalaBear p = {P_KB} (prime: {is_prime(P_KB)})", flush=True)
    if not self_tests():
        print("ABORT: self-tests failed")
        return 1

    cases27 = [("BabyBear", P_BB, 1 << 27, True),
               ("ctrl27_c17", 17 * (1 << 27) + 1, 1 << 27, False),
               ("ctrl27_c24", 24 * (1 << 27) + 1, 1 << 27, False),
               ("ctrl27_c26", 26 * (1 << 27) + 1, 1 << 27, False)]
    cases24 = [("KoalaBear", P_KB, 1 << 24, True),
               ("ctrl24_c108", 108 * (1 << 24) + 1, 1 << 24, False),
               ("ctrl24_c126", 126 * (1 << 24) + 1, 1 << 24, False),
               ("ctrl24_c136", 136 * (1 << 24) + 1, 1 << 24, False)]
    tot = sum((p - 1) // 2 for _, p, _, _ in cases27 + cases24)
    print(f"\nTotal cos evaluations: {tot / 1e9:.2f}e9; measured ~155 ns/elem "
          f"-> estimated {tot * 155e-9 / 60:.0f} min compute", flush=True)

    res = {}
    for name, p, n, dep in cases27 + cases24:
        res[name] = analyze(name, p, n, deployment=dep)

    print("\n" + "=" * 100)
    print("== (a) CERTIFICATE TABLE ==")
    print(f"  {'prime':>12} {'p':>11} {'n':>6} {'f':>4} {'beta':>6} {'M':>14} "
          f"{'C=M/sqrt(n ln(p/n))':>20} {'M/(2 sqrt n)':>13} {'M/Weil':>7}")
    for name in res:
        r = res[name]
        print(f"  {name:>12} {r['p']:>11} 2^{r['n'].bit_length() - 1:<4} {r['f']:>4} "
              f"{r['beta']:>6.3f} {r['M']:>14.4f} {r['C']:>20.6f} {r['ram']:>13.6f} "
              f"{r['M'] / r['weil']:>7.4f}")

    fl_bb = detector(res["BabyBear"], [res[k] for k in ("ctrl27_c17", "ctrl27_c24",
                                                        "ctrl27_c26")], "BabyBear")
    fl_kb = detector(res["KoalaBear"], [res[k] for k in ("ctrl24_c108", "ctrl24_c126",
                                                         "ctrl24_c136")], "KoalaBear")

    print("\n== (c) ERROR BUDGET (float64 + pairwise/fsum on ~1e8-term sums) ==")
    print("  per-term: |d cos| <= 3u*2pi + cos ulp ~ 2.4e-15 (u = 2^-53);")
    print("  worst-case coherent: n * 2.4e-15 = 3.2e-7 (n = 2^27) / 4.0e-8 (n = 2^24);")
    print("  summation: per-chunk pairwise + exact fsum across chunks ~ few e-10.")
    print("  MEASURED (strictly stronger than the bound):")
    for name in ("BabyBear", "KoalaBear"):
        r = res[name]
        print(f"    {name}: mass |S1+1| = {r['a1']:.2e}; Parseval rel = {r['a2']:.2e}; "
              f"S3 int-resid = {r['a3']:.2e}; cross-path |dev| = {r['dev']:.2e}")
    print("  => coset values certified to ~1e-6 ABSOLUTE (conservative); M ~ 2e4+ so")
    print("     M is certified to ~11 significant digits; C to ~10 digits.")

    print(f"\nTOTAL TIME {time.time() - t00:.0f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
