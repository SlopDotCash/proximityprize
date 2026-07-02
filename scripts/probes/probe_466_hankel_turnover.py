#!/usr/bin/env python3
"""
probe_466_hankel_turnover.py -- Lane P4: Hankel / Jacobi-turnover structure probe (#466).

Dossier v3 Tier-1 item 3 ("the one surviving non-magnitude seam").

Form D of the core: mu_emp = empirical spectral measure of {eta_b : b != 0} where
eta_b = sum_{x in mu_n} e(b x / p).  Since n is even, -1 in mu_n, so eta_b is REAL
(verified numerically).  eta_b is constant on cosets of mu_n in F_p^x, so mu_emp is
the UNIFORM measure on the m = (p-1)/n Gauss-period values.

We compute the Jacobi (three-term recurrence) coefficients a_k, b_k of mu_emp via the
Stieltjes/Lanczos procedure (float64, double full reorthogonalization; validated against
an mpmath dps=40 end-to-end recomputation at n=8 and exact-moment self-tests).

CHAR-0 REFERENCE (important refinement over the bare Hermite law b_k^2 = n k):
the char-0 model measure is the law of X = sum_{j=1}^{n/2} 2 cos(theta_j), theta iid
uniform; its moments are m_{2r} = (2r)! [x^r] I_0(2 sqrt x)^{n/2} (r=1: n; r=2: 3n^2-3n,
matching the known clean E_2).  Its Jacobi coefficients b_k^{(0)} are computed EXACTLY
(rational moments + Chebyshev algorithm at dps=1200).  b_k^{(0)2} ~ n k for k << n/4 and
turns over at the char-0 support edge [-n, n].  The p-signal is therefore measured by
    q_j = b_j^2(data) / b_j^{(0)2}          (char-0-normalized ramp)
and the turnover k* = first j with q_j < 0.9 (linearly interpolated), with the bare
Hermite ratio r_j = b_j^2/(n j) reported alongside.

TESTS (decision rule from the lane brief):
 (i)   spacing law: is b_{j+1}^2 - b_j^2 <= n uniformly?
 (ii)  is r_j monotone decreasing after its plateau?  (also: does b_j^2 rebound after
       its global max? -- rebounds are what Hankel-PSD would have to forbid)
 (iii) short-window prediction of k*: signal-to-noise of q_j at j << k* across a
       beta-sweep at fixed n (n=16: beta 4,5,6; n=32: beta 4,5) vs the generic-pair
       spread; Hankel-determinant growth rate L_j = sum_{i<=j} ln q_i.
 (iv)  do the b_k discriminate structured primes (Fermat 65537 at n=16; 786433 = 3*2^18+1,
       v2 = 18, at n=32) EARLIER (smaller j) than the raw moments do?  z-scores at
       matched moment budget (b_j uses moments up to order 2j).

CONTROLS: synthetic iid m-samples from the char-0 law (matched m), 2 seeds each at
n=32, 64 -- if the real k* and ramp shape match the iid control, the Jacobi turnover
sees nothing beyond the independence model (dossier sec "independence form").

Regime discipline: p prime, p = 1 mod n, beta = log_n p >= 4 except where explicitly
testing beta-dependence (beta-sweep instances labelled) and the structured prime
786433 (beta = 3.92, labelled).  Never n = p-1.  >= 2 primes per n at beta ~ 4.

Precision documentation is printed in the PRECISION section of the output.
"""

import math
import sys
import time
from fractions import Fraction

import numpy as np
import mpmath as mp

K_DEPTH = 40          # Jacobi depth
THRESH = 0.9          # turnover threshold on q_j
CHAR0_DPS = 1200      # Chebyshev-algorithm precision for exact char-0 reference
MP_VALID_DPS = 40     # mpmath end-to-end validation precision (n=8)
RMAX = 12             # moment depth for test (iv)

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


def next_prime_1mod(n: int, start: int, exclude=()) -> int:
    p = start
    r = p % n
    if r != 1:
        p += (1 - r) % n
    while True:
        if p not in exclude and is_prime(p):
            return p
        p += n


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


def v2(x: int) -> int:
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


# ---------------------------------------------------------------- eta spectrum
def gauss_period_spectrum(n: int, p: int, want_imag: bool):
    """Return (eta values on the m cosets, max |imag part| or None, g)."""
    g = primitive_root(p)
    L = p - 1
    m = L // n
    R = np.empty(L, dtype=np.uint64)
    R[0] = 1
    filled = 1
    while filled < L:  # chunk-doubling power sequence g^i mod p (products < 2^52)
        step = min(filled, L - filled)
        gl = pow(g, filled, p)
        R[filled:filled + step] = (R[:step] * np.uint64(gl)) % np.uint64(p)
        filled += step
    eta = np.zeros(m)
    im = np.zeros(m) if want_imag else None
    w = 2.0 * np.pi / p
    for j in range(n):
        th = w * R[j * m:(j + 1) * m].astype(np.float64)
        eta += np.cos(th)
        if want_imag:
            im += np.sin(th)
    del R
    maximag = float(np.abs(im).max()) if want_imag else None
    return eta, maximag, g


# ---------------------------------------------------------------- Lanczos (Stieltjes)
def lanczos(x: np.ndarray, K: int, passes: int = 2):
    """Jacobi coefficients of the uniform measure on nodes x.
    Returns (a[0..K-1], b[0..K-1]) with b[j-1] = b_j (1-indexed off-diagonals)."""
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
        for _ in range(passes):  # full reorthogonalization
            c = V[:, :k + 1].T @ u
            u -= V[:, :k + 1] @ c
        nb = float(np.linalg.norm(u))
        b[k] = nb
        if nb <= 1e-13 * scale:
            return a[:k + 1], b[:k + 1]
        V[:, k + 1] = u / nb
    return a, b


# ---------------------------------------------------------------- char-0 reference
def char0_moments_fraction(n: int, rmax: int):
    """Exact moments m_{2r}, r = 0..rmax, of X = sum_{j<=n/2} 2 cos(theta_j):
    m_{2r} = (2r)! [x^r] I_0(2 sqrt x)^{n/2}."""
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
    beta_k = b_k^2 for k >= 1 (beta_0 = m_0). Run inside mp.workdps."""
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
    """b_j^{(0)2} for j = 1..K-1 of the exact char-0 reference measure (array index j;
    entry 0 is nan)."""
    key = (n, K)
    if key in _char0_cache:
        return _char0_cache[key]
    mu = char0_moments_fraction(n, K)  # m_{2r}, r <= K
    with mp.workdps(CHAR0_DPS):
        moms = []
        for l in range(2 * K):
            if l % 2 == 0:
                f = mu[l // 2]
                moms.append(mp.mpf(f.numerator) / mp.mpf(f.denominator))
            else:
                moms.append(mp.mpf(0))
        _, betas = chebyshev_moments_to_jacobi(moms, K)
        out = np.full(K, np.nan)
        for j in range(1, K):
            out[j] = float(betas[j])
    _char0_cache[key] = out
    return out


# ---------------------------------------------------------------- mp validation
def eta_mp(n: int, p: int, dps: int):
    g = primitive_root(p)
    m = (p - 1) // n
    with mp.workdps(dps):
        tp = 2 * mp.pi / p
        et = []
        for i in range(m):
            s = mp.mpf(0)
            for j in range(n):
                s += mp.cos(tp * pow(g, j * m + i, p))
            et.append(s)
    return et


def lanczos_mp(xs, K, dps):
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
                    c = mp.fsum(vv[i] * u[i] for i in range(msz))
                    u = [u[i] - c * vv[i] for i in range(msz)]
            nb = mp.sqrt(mp.fsum(t * t for t in u))
            b.append(nb)
            V.append([t / nb for t in u])
        return [float(t) for t in a], [float(t) for t in b]


# ---------------------------------------------------------------- per-instance analysis
def kstar_interp(q, thresh):
    """q indexed j = 1..len; first crossing below thresh, linearly interpolated
    (q_0 := 1). Returns (interp value, integer first index) or (None, None)."""
    prev = 1.0
    for j in range(1, len(q) + 1):
        cur = q[j - 1]
        if cur < thresh:
            if prev == cur:
                return float(j), j
            return (j - 1) + (prev - thresh) / (prev - cur), j
        prev = cur
    return None, None


def analyze_nodes(n, nodes, tag, lnpn, p=None):
    """Full Jacobi analysis of the uniform measure on `nodes`."""
    t0 = time.time()
    msz = nodes.size
    a, b = lanczos(nodes, K_DEPTH, passes=2)
    a1, b1 = lanczos(nodes, K_DEPTH, passes=1)
    Keff = len(b)
    bsq = b ** 2
    reorth_dev = float(np.max(np.abs(bsq[:len(b1)] - b1 ** 2)
                              / (n * np.arange(1, len(b1) + 1))))
    b0 = char0_bsq(n, K_DEPTH)  # index j = 1..K-1
    J = min(Keff, K_DEPTH - 1)
    q = np.array([bsq[j - 1] / b0[j] for j in range(1, J + 1)])
    rj = np.array([bsq[j - 1] / (n * j) for j in range(1, Keff + 1)])
    M = float(np.abs(nodes).max())
    xmax, xmin = float(nodes.max()), float(nodes.min())
    ks, ksj = kstar_interp(q, THRESH)
    ks80, _ = kstar_interp(q, 0.8)
    ks95, _ = kstar_interp(q, 0.95)
    ksH, _ = kstar_interp(rj[:J], THRESH)  # bare-Hermite turnover for reference
    # (i) spacing
    spac = np.diff(np.concatenate([[0.0], bsq])) / n  # spac[j-1] = (b_j^2-b_{j-1}^2)/n
    # (ii) monotonicity of r_j after peak / bsq rebound after argmax
    jpk = int(np.argmax(rj))
    viol_r = int(np.sum(np.diff(rj[jpk:]) > 1e-3))
    maxup_r = float(np.max(np.diff(rj[jpk:]), initial=-np.inf))
    jbm = int(np.argmax(bsq))
    reb = np.diff(bsq[jbm:]) / n
    viol_b = int(np.sum(reb > 0.02))
    maxreb = float(np.max(reb, initial=-np.inf))
    # moments (for test iv)
    mr = np.array([float(np.mean(nodes ** (2 * r))) for r in range(1, RMAX + 1)])
    mu0 = char0_moments_fraction(n, RMAX)
    mrat = np.array([mr[r - 1] / float(mu0[r]) for r in range(1, RMAX + 1)])
    res = dict(n=n, p=p, tag=tag, m=msz, lnpn=lnpn, M=M, xmax=xmax, xmin=xmin,
               C=(M / math.sqrt(n * lnpn) if lnpn > 0 else float('nan')),
               bsq=bsq, q=q, rj=rj, ks=ks, ksj=ksj, ks80=ks80, ks95=ks95, ksH=ksH,
               spacmax=float(spac.max()), spacarg=int(np.argmax(spac)) + 1,
               nviol_spac=int(np.sum(spac > 1.02)),
               jpk=jpk, viol_r=viol_r, maxup_r=maxup_r,
               jbm=jbm + 1, viol_b=viol_b, maxreb=maxreb,
               bmax=float(b.max()), argbmax=int(np.argmax(b)) + 1,
               maxabs_a=float(np.abs(a).max()), mrat=mrat,
               reorth_dev=reorth_dev, secs=time.time() - t0)
    return res


def analyze_prime(n, p, tag):
    t0 = time.time()
    want_imag = p < 3_000_000
    eta, maximag, g = gauss_period_spectrum(n, p, want_imag)
    msz = eta.size
    s1, s2 = float(eta.sum()), float((eta ** 2).sum())
    # exact identities: sum_i eta_i = -1 ; sum_i eta_i^2 = p - n
    chk1 = abs(s1 + 1.0)
    chk2 = abs(s2 / (p - n) - 1.0)
    assert chk1 < 1e-6 and chk2 < 1e-9, (n, p, s1, s2)
    lnpn = math.log(p / n)
    res = analyze_nodes(n, eta, tag, lnpn, p=p)
    res.update(maximag=maximag, g=g, chk1=chk1, chk2=chk2,
               v2p=v2(p - 1), beta=math.log(p) / math.log(n),
               secs=time.time() - t0)
    return res, eta


def sample_char0(n, msz, seed):
    rng = np.random.default_rng(seed)
    th = rng.uniform(0.0, 2.0 * np.pi, size=(msz, n // 2))
    return (2.0 * np.cos(th)).sum(axis=1)


# ---------------------------------------------------------------- self tests
def self_tests():
    print("== SELF-TESTS ==")
    # 1. Chebyshev on Gaussian moments -> beta_k = k
    K = 20
    with mp.workdps(300):
        moms = []
        for l in range(2 * K):
            moms.append(mp.mpf(0) if l % 2 else
                        mp.mpf(math.prod(range(l - 1, 0, -2)) if l else 1))
        _, betas = chebyshev_moments_to_jacobi(moms, K)
        errg = max(abs(float(betas[k]) - k) for k in range(1, K))
    print(f"  Chebyshev(Gaussian moments): max |beta_k - k| = {errg:.2e}  (want ~0)")
    # 2. Lanczos vs Chebyshev on a small explicit discrete measure
    nodes = np.array([-5.0, -3.5, -2.0, -1.0, -0.25, 0.5, 1.25, 2.0, 3.0, 4.5, 5.5, 6.0])
    K2 = 6
    a, b = lanczos(nodes, K2)
    with mp.workdps(300):
        moms = [mp.fsum(mp.mpf(x) ** l for x in nodes) / len(nodes)
                for l in range(2 * K2)]
        al, be = chebyshev_moments_to_jacobi(moms, K2)
        errl = max(abs(b[k - 1] ** 2 - float(be[k])) for k in range(1, K2))
        erra = max(abs(a[k] - float(al[k])) for k in range(K2))
    print(f"  Lanczos vs Chebyshev (12-node measure): max|b^2 diff|={errl:.2e}, "
          f"max|a diff|={erra:.2e}")
    # 3. char-0 reference sanity: b_1^2 = n, b_2^2 = (2 - 3/n) n
    for n in (8, 16, 32, 64):
        b0 = char0_bsq(n, K_DEPTH)
        e1 = abs(b0[1] - n)
        e2 = abs(b0[2] - (2 - 3.0 / n) * n)
        mu = char0_moments_fraction(n, 2)
        assert mu[1] == n and mu[2] == 3 * n * n - 3 * n, (n, mu)
        print(f"  char-0 n={n}: |b1^2-n|={e1:.2e}, |b2^2-(2-3/n)n|={e2:.2e}, "
              f"E2={mu[2]} (=3n^2-3n ok), b_39^2={b0[39]:.3f} (support edge n^2/4={n*n/4})")
    assert errg < 1e-9 and errl < 1e-9 and erra < 1e-9
    print()


# ---------------------------------------------------------------- main
def main():
    t00 = time.time()
    print("probe_466_hankel_turnover.py  --  Lane P4 Hankel/Jacobi-turnover probe")
    print(f"K_DEPTH={K_DEPTH} THRESH={THRESH} CHAR0_DPS={CHAR0_DPS} RMAX={RMAX}")
    print()
    self_tests()

    # ---------------- instance list
    plan = []  # (n, beta, p_fixed, tag)
    p8a = next_prime_1mod(8, 8 ** 4)
    p8b = next_prime_1mod(8, p8a + 8)
    plan += [(8, 4.0, p8a, "gen1"), (8, 4.0, p8b, "gen2")]
    plan += [(16, 4.0, 65537, "FERMAT")]
    p16a = next_prime_1mod(16, 16 ** 4, exclude=(65537,))
    p16b = next_prime_1mod(16, p16a + 16, exclude=(65537,))
    plan += [(16, 4.0, p16a, "gen1"), (16, 4.0, p16b, "gen2")]
    plan += [(16, 5.0, next_prime_1mod(16, 16 ** 5), "beta5")]
    plan += [(16, 6.0, next_prime_1mod(16, 16 ** 6), "beta6")]
    p32a = next_prime_1mod(32, 32 ** 4)
    p32b = next_prime_1mod(32, p32a + 32)
    plan += [(32, 4.0, p32a, "gen1"), (32, 4.0, p32b, "gen2")]
    plan += [(32, 3.92, 786433, "HIGHV2")]  # 3*2^18+1, v2(p-1)=18, beta=3.92 (structured)
    plan += [(32, 5.0, next_prime_1mod(32, 32 ** 5), "beta5")]
    p64a = next_prime_1mod(64, 64 ** 4)
    p64b = next_prime_1mod(64, p64a + 64)
    plan += [(64, 4.0, p64a, "gen1"), (64, 4.0, p64b, "gen2")]

    results = []
    eta_keep = {}
    print("== INSTANCES ==")
    for (n, beta, p, tag) in plan:
        assert p % n == 1 and is_prime(p) and p - 1 != n
        res, eta = analyze_prime(n, p, tag)
        results.append(res)
        if (n, tag) == (8, "gen1"):
            eta_keep[(n, tag)] = eta.copy()
        mi = res['maximag']
        mistr = f"{mi:.1e}" if mi is not None else "skip"
        print(f"  n={n:3d} p={p:9d} [{tag:7s}] beta={res['beta']:.3f} m={res['m']:8d} "
              f"v2(p-1)={res['v2p']:2d} ln(p/n)={res['lnpn']:6.3f} M={res['M']:7.3f} "
              f"C={res['C']:5.3f} maximag={mistr} "
              f"chk(sum=-1)={res['chk1']:.1e} chk(Parseval)={res['chk2']:.1e} "
              f"[{res['secs']:.1f}s]")

    # synthetic iid char-0 controls, m matched to the n=32/n=64 gen1 instances
    print("\n== SYNTHETIC IID CONTROLS (char-0 law, matched m) ==")
    for n, mref in ((32, next(r['m'] for r in results if r['n'] == 32 and r['tag'] == 'gen1')),
                    (64, next(r['m'] for r in results if r['n'] == 64 and r['tag'] == 'gen1'))):
        for seed in (1, 2):
            nodes = sample_char0(n, mref, seed)
            res = analyze_nodes(n, nodes, f"SYNTH-s{seed}", math.log(mref))
            results.append(res)
            print(f"  n={n:3d} m={mref:8d} [SYNTH-s{seed}] ln(m)={math.log(mref):6.3f} "
                  f"M={res['M']:7.3f} [{res['secs']:.1f}s]")

    # ---------------- PRECISION section
    print("\n== PRECISION ==")
    print("  float64 pipeline: eta abs err <~ n*1e-15; Lanczos double full-reorth.")
    print("  1-pass vs 2-pass reorth max scaled dev per instance "
          "(max_j |b_j^2(1p)-b_j^2(2p)|/(n j)):")
    for r in results:
        print(f"    n={r['n']:3d} [{r['tag']:9s}] reorth_dev={r['reorth_dev']:.2e}")
    r8 = next(r for r in results if r['n'] == 8 and r['tag'] == 'gen1')
    print(f"  mpmath end-to-end validation (n=8 gen1, p={r8['p']}, dps={MP_VALID_DPS}, "
          f"K={K_DEPTH}) ... ", end="", flush=True)
    t0 = time.time()
    etm = eta_mp(8, r8['p'], MP_VALID_DPS)
    erreta = max(abs(float(etm[i]) - eta_keep[(8, 'gen1')][i]) for i in range(len(etm)))
    amp, bmp = lanczos_mp(etm, K_DEPTH, MP_VALID_DPS)
    errb = max(abs(bmp[k] ** 2 - r8['bsq'][k]) / (8 * (k + 1)) for k in range(K_DEPTH))
    print(f"[{time.time() - t0:.1f}s]")
    print(f"    max |eta_f64 - eta_mp| = {erreta:.2e}; "
          f"max_j |b_j^2 - b_j^2(mp)|/(nj) = {errb:.2e}")

    # ---------------- per-instance ramp tables
    print("\n== RAMP TABLES (q_j = b_j^2 / b_j^{(0)2} char-0-normalized; "
          "r_j = b_j^2/(nj) bare-Hermite) ==")
    for r in results:
        pstr = str(r['p']) if r['p'] else "iid"
        print(f"\n  n={r['n']} p={pstr} [{r['tag']}]  M={r['M']:.3f} xmax={r['xmax']:.3f} "
              f"xmin={r['xmin']:.3f}  M^2/2n={r['M'] ** 2 / (2 * r['n']):.2f} "
              f"M^2/4n={r['M'] ** 2 / (4 * r['n']):.2f} "
              f"(xmax-xmin)^2/16n={(r['xmax'] - r['xmin']) ** 2 / (16 * r['n']):.2f}")
        print(f"    k*(q<{THRESH})={fmt(r['ks'])} [k*(0.95)={fmt(r['ks95'])}, "
              f"k*(0.8)={fmt(r['ks80'])}]  k*_Hermite(r<{THRESH})={fmt(r['ksH'])}  "
              f"ln(p/n)={r['lnpn']:.3f}  2*max_b={2 * r['bmax']:.3f} (argmax j={r['argbmax']}) "
              f"vs M={r['M']:.3f}  max|a_k|={r['maxabs_a']:.3f}")
        qs = "  ".join(f"{r['q'][j - 1]:.4f}" for j in range(1, min(21, len(r['q']) + 1)))
        rs = "  ".join(f"{r['rj'][j - 1]:.4f}" for j in range(1, min(21, len(r['rj']) + 1)))
        print(f"    q_1..20: {qs}")
        print(f"    r_1..20: {rs}")

    # ---------------- TEST (i): spacing law
    print(f"\n== TEST (i): spacing law (b_{{j+1}}^2 - b_j^2 <= n ?) ==")
    ok = True
    for r in results:
        flag = "OK " if r['nviol_spac'] == 0 else "VIOLATED"
        if r['nviol_spac'] > 0:
            ok = False
        print(f"  n={r['n']:3d} [{r['tag']:9s}] max spacing/n = {r['spacmax']:7.4f} "
              f"at j={r['spacarg']:2d}; #viol(>1.02) = {r['nviol_spac']}  {flag}")
    b0chk = []
    for n in (8, 16, 32, 64):
        b0 = char0_bsq(n, K_DEPTH)
        sp = np.diff(np.concatenate([[0.0], b0[1:]])) / n
        b0chk.append((n, float(np.nanmax(sp))))
    print("  char-0 reference max spacing/n: " +
          ", ".join(f"n={n}: {s:.4f}" for n, s in b0chk))
    print(f"  TEST (i) VERDICT: {'HOLDS on all instances' if ok else 'FAILS somewhere'}")

    # ---------------- TEST (ii): monotone decay after plateau + rebounds
    print(f"\n== TEST (ii): r_j monotone decreasing after peak?  b_j^2 rebounds after max? ==")
    for r in results:
        print(f"  n={r['n']:3d} [{r['tag']:9s}] r-peak at j={r['jpk'] + 1:2d}; "
              f"#r-increases after peak = {r['viol_r']:2d} (max up-step {r['maxup_r']:+.2e}); "
              f"b^2-argmax j={r['jbm']:2d}; #b^2 rebounds(>0.02n) = {r['viol_b']:2d} "
              f"(max rebound/n = {r['maxreb']:+.3f})")

    # ---------------- TEST (iii): short-window prediction of k*
    print(f"\n== TEST (iii): short-window functionals vs k* ==")
    for n, tags in ((16, ["gen1", "gen2", "beta5", "beta6", "FERMAT"]),
                    (32, ["gen1", "gen2", "beta5", "HIGHV2"])):
        grp = [r for r in results if r['n'] == n and r['tag'] in tags]
        gen = [r for r in grp if r['tag'].startswith('gen')]
        print(f"\n  GROUP n={n}: k* per instance: " +
              ", ".join(f"{r['tag']}={fmt(r['ks'])}" for r in grp))
        print(f"    {'j':>2s}  {'noise |q_gen1-q_gen2|':>22s}  "
              f"{'signal max|q_beta - mean(gen)|':>30s}  {'SNR':>8s}")
        for j in range(1, 13):
            noise = abs(gen[0]['q'][j - 1] - gen[1]['q'][j - 1])
            gm = 0.5 * (gen[0]['q'][j - 1] + gen[1]['q'][j - 1])
            others = [r for r in grp if r['tag'].startswith('beta')]
            sig = max(abs(r['q'][j - 1] - gm) for r in others) if others else float('nan')
            snr = sig / noise if noise > 0 else float('inf')
            print(f"    {j:2d}  {noise:22.3e}  {sig:30.3e}  {snr:8.2f}")
        # cumulative Hankel-det growth defect L_j = sum_{i<=j} ln q_i
        print("    Hankel log-det defect L_j = sum_{i<=j} ln q_i at j=3,5:")
        for r in grp:
            L3 = float(np.sum(np.log(r['q'][:3])))
            L5 = float(np.sum(np.log(r['q'][:5])))
            print(f"      [{r['tag']:7s}] L_3={L3:+.4e} L_5={L5:+.4e} k*={fmt(r['ks'])}")

    # global k* vs ln(p/n) fit on non-saturated prime instances (M < 0.75 n)
    fitset = [r for r in results if r['p'] and r['M'] < 0.75 * r['n']]
    satset = [r for r in results if r['p'] and r['M'] >= 0.75 * r['n']]
    print("\n  saturated instances (M >= 0.75n, support-limited -- excluded from fit): " +
          ", ".join(f"n={r['n']}[{r['tag']}] M/n={r['M'] / r['n']:.2f}" for r in satset))
    if len(fitset) >= 3 and all(r['ks'] for r in fitset):
        xs = np.array([r['lnpn'] for r in fitset])
        ys = np.array([r['ks'] for r in fitset])
        A = np.vstack([xs, np.ones_like(xs)]).T
        (sl, ic), res_, *_ = np.linalg.lstsq(A, ys, rcond=None)
        yh = A @ np.array([sl, ic])
        ss = 1 - np.sum((ys - yh) ** 2) / np.sum((ys - ys.mean()) ** 2)
        print(f"  FIT k* = {sl:.3f} * ln(p/n) + {ic:+.3f}   R^2 = {ss:.4f}   "
              f"(N={len(fitset)} non-saturated prime instances)")
        for r in fitset:
            print(f"    n={r['n']:3d} [{r['tag']:7s}] ln(p/n)={r['lnpn']:6.3f} "
                  f"k*={r['ks']:6.3f} M^2/4n={r['M'] ** 2 / (4 * r['n']):6.3f} "
                  f"M^2/2n={r['M'] ** 2 / (2 * r['n']):6.3f} "
                  f"k*/ln(p/n)={r['ks'] / r['lnpn']:.3f}")

    # real vs iid-control comparison
    print("\n  REAL vs IID CONTROL (independence-model consistency):")
    for n in (32, 64):
        real = [r for r in results if r['n'] == n and r['tag'] == 'gen1']
        syn = [r for r in results if r['n'] == n and r['tag'].startswith('SYNTH')]
        for r in real + syn:
            print(f"    n={n:3d} [{r['tag']:9s}] k*={fmt(r['ks'])} M={r['M']:.3f} "
                  f"q_1..6 = " + " ".join(f"{r['q'][j]:.4f}" for j in range(6)))

    # ---------------- TEST (iv): structured-prime discrimination, b_j vs moments
    print(f"\n== TEST (iv): structured primes -- b_j vs raw moments at matched budget ==")
    for n, stag in ((16, "FERMAT"), (32, "HIGHV2")):
        grp = [r for r in results if r['n'] == n and r['p']]
        gen = [r for r in grp if r['tag'].startswith('gen')]
        st = next(r for r in grp if r['tag'] == stag)
        print(f"\n  n={n}: structured [{stag}] p={st['p']} (v2(p-1)={st['v2p']}, "
              f"beta={st['beta']:.3f}) vs generics "
              f"{[g_['p'] for g_ in gen]} (v2={[g_['v2p'] for g_ in gen]})")
        if stag == "HIGHV2":
            print("    CAVEAT: 786433 has beta=3.92 vs generic beta=4.00 "
                  "(ln(p/n): {:.2f} vs {:.2f}) -- part of any deviation may be beta drift."
                  .format(st['lnpn'], gen[0]['lnpn']))
        print(f"    {'j/r':>3s} {'z_b(j) = |q^S-mean q^gen|/|q^g1-q^g2|':>38s}   "
              f"{'z_mom(r) at matched 2r=2j':>26s}")
        firstb, firstm = None, None
        for j in range(1, RMAX + 1):
            qg = [g_['q'][j - 1] for g_ in gen]
            nz = abs(qg[0] - qg[1])
            zb = abs(st['q'][j - 1] - 0.5 * (qg[0] + qg[1])) / nz if nz > 0 else float('inf')
            mg = [g_['mrat'][j - 1] for g_ in gen]
            nzm = abs(mg[0] - mg[1])
            zm = abs(st['mrat'][j - 1] - 0.5 * (mg[0] + mg[1])) / nzm if nzm > 0 else float('inf')
            if firstb is None and zb > 3:
                firstb = j
            if firstm is None and zm > 3:
                firstm = j
            print(f"    {j:3d} {zb:38.2f}   {zm:26.2f}")
        print(f"    first index with z>3:  b_j: j={firstb}   moment m_2r: r={firstm}   "
              f"(b_j is a functional of moments up to order 2j)")

    print(f"\nTOTAL TIME {time.time() - t00:.1f}s")


def fmt(x):
    return f"{x:.3f}" if x is not None else "none(>39)"


if __name__ == "__main__":
    sys.exit(main())
