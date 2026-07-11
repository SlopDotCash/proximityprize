#!/usr/bin/env python3
"""
probe_w14_hankel_sign_seam.py -- thread wall:hankel-jacobi-seam (#466, lane W14).

The assigned seam: "Hankel-positivity / Lax-pair spectral-shift at the Jacobi turnover k*"
(dossier v3 section 6 item 3).  Prior record (do NOT re-derive): bounded-window functionals are
ensemble-deterministic (466-r1-hankel-bounded-window-refuted); Toda invariants are gauge
(_AssaultV2_JacobiToda); Hankel-PSD caps the top power sum only from BELOW (_AvRR_RealRootHankelOneSided);
positivity + equal masses adds nothing over the raw moment bound (466-r2-cmk-lonespike-refuted);
odd-moment/sign LP rows are inactive in the prize regime (C076); prefix+local-slope gates are
insufficient (_JacobiFinitePrefixTurnoverGate, _JacobiLocalSlopeTurnoverGate).

What is genuinely untested and probed HERE -- the sign/positivity corners AT the turnover:

 T1 (REBOUND-ABOVE-FIRST-PEAK, arithmetic instances): is max_k b_k always attained at the FIRST
    strict local max of the b-ladder?  If a positivity law forced "no later higher peak", form D's
    "forall k" criterion (_FormDUpperBoundHankelCriterion.M_le_of_bsq_bound) would reduce to the
    early window.  Measured on the real ensemble + adversarial (Fermat / 2-power-heavy) primes
    + iid char-0 controls.

 T2 (ABSTRACT COUNTERMODEL, the kill shot for the T1 hope): does the equal-mass (uniform-atom)
    constraint forbid a later-higher b-peak for a general positive measure?  (Favard alone kills
    the non-uniform case trivially: any b-pattern is realized by SOME measure.  The uniform-weight
    case is the only residual question.)  We search two-scale uniform-atom mixtures for a
    certified rebound-above-first-peak.

 T3 (SIGN DATA AT k*): the diagonal Jacobi coefficients a_k (odd-moment/asymmetry data -- the
    one second-order channel with genuine sign structure that magnitude methods discard), the
    sign of the pre-turnover bulge q_j - 1, and the pre-turnover residual signs across matched
    prime pairs: does ANY sign statistic at j <= k* separate mu_n instances from matched iid
    controls, or predict (k*, M) across pairs?  (r1 measured magnitudes only.)

 T4 (SPECTRAL-SHIFT / INTERLACING LADDER): the Ritz edges lambda_max(J_k) and their increments
    (the Krein shift data of the truncation family).  Verify one-sidedness (edges increase to M
    from below -- so shift data is lower-bound-direction only), measure the increment scale at
    k* (r15 claim: Theta(sqrt n), not O(1)), and test whether the increment PROFILE at k*
    separates real instances from iid controls at matched (n, m).

 T5 (WINDOW <=> MOMENT LOCALITY, numeric check of the Lean brick _W14JacobiWindowMomentEquivalence):
    the depth-K Jacobi window determines the moments to order 2K exactly ((J^r)_{00} locality);
    verified numerically at moderate depth as a precision self-test.

Decision rule: a surviving seam invariant must (a) separate real instances from the iid baseline
beyond the p-deterministic drift, AND (b) act in the upper-bound direction (certify smallness of
something that caps M).  Anything failing (a) is baseline-blind; anything failing (b) is
lower-bound-direction data (the _AvRR / Kravchuk one-sidedness).

Regime discipline: p prime, p = 1 mod n, beta = log_n p ~ 4; adversarial primes labelled.
Float64 Lanczos with two-pass full reorthogonalization (the r1-validated procedure), moment
round-trip self-test printed per instance.
"""

import math
import time

import numpy as np
import mpmath as mp

K_DEPTH = 40
THRESH = 0.9
CHAR0_DPS = 1200
RNG_SEEDS = (1, 2, 3)

T0 = time.time()


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
    for a in small:
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


def v2(x: int) -> int:
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def gen_primes_1mod(n: int, start: int, count: int, max_v2: int = 6, exclude=()):
    """Generic primes p = 1 mod n with v2(p-1) <= max_v2 (excluding structured ones)."""
    out = []
    p = start + ((1 - start % n) % n)
    while len(out) < count:
        if p not in exclude and is_prime(p) and v2(p - 1) <= max_v2:
            out.append(p)
        p += n
    return out


# ---------------------------------------------------------------- eta spectrum
def gauss_periods(n: int, p: int) -> np.ndarray:
    g = primitive_root(p)
    L = p - 1
    m = L // n
    R = np.empty(L, dtype=np.uint64)
    R[0] = 1
    filled = 1
    while filled < L:
        step = min(filled, L - filled)
        gl = pow(g, filled, p)
        R[filled:filled + step] = (R[:step] * np.uint64(gl)) % np.uint64(p)
        filled += step
    eta = np.zeros(m)
    w = 2.0 * np.pi / p
    for j in range(n):
        eta += np.cos(w * R[j * m:(j + 1) * m].astype(np.float64))
    del R
    return eta


# ---------------------------------------------------------------- Lanczos
def lanczos(x: np.ndarray, K: int, passes: int = 2):
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


def jacobi_matrix(a: np.ndarray, b: np.ndarray, k: int) -> np.ndarray:
    """k x k truncation J_k from Lanczos output (a[0..], b[0..]; b[j] couples j,j+1)."""
    J = np.diag(a[:k])
    for j in range(k - 1):
        J[j, j + 1] = J[j + 1, j] = b[j]
    return J


def ritz_edges(a: np.ndarray, b: np.ndarray, K: int) -> np.ndarray:
    """lambda_max(J_k), k = 1..K."""
    K = min(K, a.size)
    out = np.zeros(K)
    for k in range(1, K + 1):
        out[k - 1] = float(np.linalg.eigvalsh(jacobi_matrix(a, b, k))[-1])
    return out


# ---------------------------------------------------------------- char-0 reference
from fractions import Fraction


def char0_moments_fraction(n: int, rmax: int):
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
    key = (n, K)
    if key in _char0_cache:
        return _char0_cache[key]
    mu = char0_moments_fraction(n, K)
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


# ---------------------------------------------------------------- instance analysis
def kstar_interp(q: np.ndarray) -> float:
    """First j with q_j < THRESH, linearly interpolated (r1 convention)."""
    for j in range(1, q.size):
        if not np.isnan(q[j]) and q[j] < THRESH:
            if j == 1 or np.isnan(q[j - 1]):
                return float(j)
            q0, q1 = q[j - 1], q[j]
            return float(j - 1 + (q0 - THRESH) / (q0 - q1))
    return float(q.size)


def analyze(x: np.ndarray, n: int, label: str, K: int = K_DEPTH):
    a, b = lanczos(x, K)
    kb = b.size
    M = float(np.abs(x).max())
    c0 = char0_bsq(n, K)
    q = np.full(kb + 1, np.nan)
    for j in range(1, min(kb + 1, K)):
        if not np.isnan(c0[j]) and c0[j] > 0:
            q[j] = (b[j - 1] ** 2) / c0[j]
    ks = kstar_interp(q)
    # first strict local max of b_1..b_kb (index 1-based)
    k1 = None
    for j in range(1, kb):
        if b[j] < b[j - 1]:
            k1 = j  # b_{k1} (1-based) = b[k1-1] is first descent point
            break
    peak1 = float(b[:k1].max()) if k1 else float(b.max())
    kg = int(np.argmax(b)) + 1  # 1-based global argmax
    rebound = (k1 is not None) and (kg > k1) and (b[kg - 1] > peak1 * (1 + 1e-9))
    edges = ritz_edges(a, b, kb)
    # moment round-trip self-test: (J^r)_00 * ? -- moments of uniform measure directly
    xs = x / math.sqrt(n)  # scale for conditioning
    mom_direct = [float(np.mean(xs ** r)) for r in range(13)]
    Jfull = jacobi_matrix(a, b, min(kb, 8)) / math.sqrt(n)
    Jr = np.eye(Jfull.shape[0])
    mom_win = []
    for r in range(13):
        mom_win.append(float(Jr[0, 0]))
        Jr = Jr @ Jfull
    rel = max(abs(mom_win[r] - mom_direct[r]) / max(abs(mom_direct[r]), 1e-30)
              for r in range(1, 13))
    return dict(label=label, n=n, m=x.size, a=a, b=b, q=q, kstar=ks, M=M,
                k1=k1, kg=kg, peak1=peak1, rebound=rebound, edges=edges,
                mom_roundtrip_relerr=rel)


def iid_char0_sample(n: int, m: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    th = rng.uniform(0.0, 2.0 * np.pi, size=(m, n // 2))
    return (2.0 * np.cos(th)).sum(axis=1)


# ---------------------------------------------------------------- report helpers
def fmt_signs(v, upto):
    return "".join("+" if t > 0 else "-" for t in v[:upto])


def main():
    print("=" * 100)
    print("probe_w14_hankel_sign_seam.py -- sign/positivity corners at the Jacobi turnover k*")
    print("=" * 100)

    # ---------------- instance set ----------------
    instances = []
    # n=16, beta ~ 4: Fermat + 2-power-heavy + generics
    n = 16
    gens16 = gen_primes_1mod(16, 65600, 4, max_v2=6, exclude=(65537,))
    for p, tag in ([(65537, "FERMAT")] +
                   [(114689, "POW2-v14")] + [(163841, "POW2-v15")] +
                   [(pp, f"gen{i+1}") for i, pp in enumerate(gens16)]):
        assert is_prime(p) and (p - 1) % n == 0, (p, n)
        instances.append((n, p, tag))
    # n=32: structured 786433 + NTT 995329 + generics
    n = 32
    gens32 = gen_primes_1mod(32, 1048576, 3, max_v2=6)
    for p, tag in ([(786433, "POW2-v18")] + [(995329, "POW2-v12")] +
                   [(pp, f"gen{i+1}") for i, pp in enumerate(gens32)]):
        assert is_prime(p) and (p - 1) % n == 0, (p, n)
        instances.append((n, p, tag))
    # n=64: two generics near 2^24 + one 2-power-heavy
    n = 64
    gens64 = gen_primes_1mod(64, 16777216, 2, max_v2=8)
    cand64 = []
    for c in range(17, 40, 2):
        p = c * (1 << 20) + 1
        if is_prime(p) and (p - 1) % 64 == 0:
            cand64.append(p)
    for p, tag in ([(pp, f"gen{i+1}") for i, pp in enumerate(gens64)] +
                   ([(cand64[0], f"POW2-v{v2(cand64[0]-1)}")] if cand64 else [])):
        instances.append((n, p, tag))

    results = []
    print("\n== INSTANCES (arithmetic mu_n Gauss-period measures) ==")
    for (n, p, tag) in instances:
        t0 = time.time()
        eta = gauss_periods(n, p)
        r = analyze(eta, n, tag)
        r.update(p=p, beta=math.log(p) / math.log(n), v2=v2(p - 1), kind="real")
        results.append(r)
        print(f"  n={n:3d} p={p:9d} [{tag:9s}] beta={r['beta']:.3f} v2={r['v2']:2d} "
              f"m={r['m']:7d} M={r['M']:8.3f} k*={r['kstar']:6.3f} "
              f"k1(first-descent)={r['k1']} kg(argmax)={r['kg']} "
              f"rebound_above_first_peak={r['rebound']} "
              f"roundtrip_relerr={r['mom_roundtrip_relerr']:.2e} ({time.time()-t0:.1f}s)")

    print("\n== IID CHAR-0 CONTROLS (matched m; the independence baseline) ==")
    controls = []
    for (n, m) in [(16, 4096), (32, 32768), (64, 262144)]:
        for s in RNG_SEEDS:
            x = iid_char0_sample(n, m, seed=1000 * n + s)
            r = analyze(x, n, f"SYNTH-s{s}")
            r.update(p=None, beta=None, v2=None, kind="iid")
            controls.append(r)
            print(f"  n={n:3d} m={m:7d} [SYNTH-s{s}] M={r['M']:8.3f} k*={r['kstar']:6.3f} "
                  f"k1={r['k1']} kg={r['kg']} rebound={r['rebound']} "
                  f"roundtrip_relerr={r['mom_roundtrip_relerr']:.2e}")

    # ---------------- T1 verdict ----------------
    print("\n== T1: REBOUND-ABOVE-FIRST-PEAK (arithmetic + control census) ==")
    nreb_real = sum(1 for r in results if r["rebound"])
    nreb_iid = sum(1 for r in controls if r["rebound"])
    print(f"  real instances with global argmax_b AFTER first descent and ABOVE first peak: "
          f"{nreb_real}/{len(results)}")
    print(f"  iid controls  with rebound-above-first-peak: {nreb_iid}/{len(controls)}")
    for r in results + controls:
        if r["rebound"]:
            b = r["b"]
            print(f"    REBOUND: n={r['n']} [{r['label']}] k1={r['k1']} kg={r['kg']} "
                  f"peak1={r['peak1']:.4f} b_kg={b[r['kg']-1]:.4f} "
                  f"ratio={b[r['kg']-1]/r['peak1']:.4f}")

    # ---------------- T2 abstract countermodel ----------------
    print("\n== T2: ABSTRACT UNIFORM-ATOM COUNTERMODEL (does equal-mass positivity forbid a")
    print("        later-HIGHER b-peak?  Favard already kills the non-uniform case.) ==")
    found = None
    # Design: bulk arcsine grid on [-1,1] (m-2 atoms; its b-ladder starts at 1/sqrt(2) and
    # DESCENDS toward the asymptotic 1/2 -- an immediate first peak) + ONE far pair {-W, +W}.
    # After the Krylov space captures the pair (delay grows with log m / log W), realizing the
    # edge eigenvalue +-W in a Jacobi matrix with bounded diagonal forces (Gershgorin)
    # max_k (b_{k-1} + b_k) >= W - max|a|, i.e. a LATE b-peak >= ~(W - max|a|)/2 >> peak1.
    for mtot in (1024, 4096, 16384):
        for W in (2.5, 3.0, 4.0, 6.0):
            mc = mtot - 2
            uc = (np.arange(mc) + 0.5) / mc
            core = np.cos(np.pi * (1 - uc))  # monotone grid in [-1,1]
            x = np.concatenate([core, [-W, W]])
            a, b = lanczos(x, K_DEPTH)
            k1 = None
            for j in range(1, b.size):
                if b[j] < b[j - 1]:
                    k1 = j
                    break
            if k1 is None:
                continue
            peak1 = float(b[:k1].max())
            kg = int(np.argmax(b)) + 1
            if kg > k1 and b[kg - 1] > peak1 * 1.05:
                ratio = b[kg - 1] / peak1
                if found is None or ratio > found[0]:
                    found = (ratio, mtot, W, k1, kg, peak1, float(b[kg - 1]), b.copy())
    if found:
        ratio, mtot, W, k1, kg, peak1, bkg, b = found
        print(f"  COUNTERMODEL FOUND (strongest in grid): uniform measure on {mtot} atoms =")
        print(f"    arcsine grid on [-1,1] ({mtot-2} atoms) + one far pair {{-W,+W}}, W={W}")
        print(f"    b-ladder: " + " ".join(f"{t:.3f}" for t in b[:min(20, b.size)]))
        print(f"    first descent at k1={k1} (peak1={peak1:.4f}); global argmax kg={kg} "
              f"with b_kg={bkg:.4f} = {ratio:.2f} x peak1")
        print("    => equal-mass positivity does NOT forbid a later-HIGHER b-peak: the")
        print("       'no-second-higher-peak' reduction of the forall-k form-D criterion to")
        print("       the early window is abstractly FALSE even under the uniform-atom")
        print("       constraint (Favard already kills the non-uniform case).")
    else:
        print("  no countermodel found in the bulk+far-pair grid -- WEAK evidence only; "
              "does NOT establish a positivity law.")

    # ---------------- T3 sign data at k* ----------------
    print("\n== T3: SIGN DATA AT/BELOW k* ==")
    print("  (i) diagonal Jacobi coefficients a_k (odd-moment channel), normalized a_k/sqrt(n):")
    for r in results + controls:
        a, n = r["a"], r["n"]
        upto = min(12, a.size)
        s = " ".join(f"{t/math.sqrt(n):+.4f}" for t in a[:upto])
        print(f"    n={n:3d} [{r['label']:9s}] ({r['kind']}) a_0..a_{upto-1}/sqrt(n) = {s}")
    print("  per-cell |a_k|/sqrt(n) scale (mean over k<=8) real vs iid:")
    for n in (16, 32, 64):
        sc_r = [np.mean(np.abs(r["a"][:8])) / math.sqrt(n) for r in results if r["n"] == n]
        sc_i = [np.mean(np.abs(r["a"][:8])) / math.sqrt(n) for r in controls if r["n"] == n]
        print(f"    n={n:3d}: real {np.mean(sc_r):.5f} +- {np.std(sc_r):.5f}   "
              f"iid {np.mean(sc_i):.5f} +- {np.std(sc_i):.5f}")

    print("  (ii) pre-turnover bulge signs sign(q_j - 1), j = 1..8:")
    for r in results + controls:
        q = r["q"]
        sg = fmt_signs([q[j] - 1 if not np.isnan(q[j]) else 0 for j in range(1, 9)], 8)
        print(f"    n={r['n']:3d} [{r['label']:9s}] ({r['kind']}) v2={r['v2']} "
              f"signs(q_1..8 - 1) = {sg}  k*={r['kstar']:.2f}")

    print("  (iii) matched-pair residual-sign prediction test (does the sign pattern of")
    print("        q_j(A)-q_j(B) for j <= 4 predict sign of k*(A)-k*(B) / M(A)-M(B)?):")
    pairs = []
    for n in (16, 32):
        rs = [r for r in results if r["n"] == n and r["kind"] == "real"]
        for i in range(len(rs)):
            for j in range(i + 1, len(rs)):
                pairs.append((rs[i], rs[j]))
    agree_k, agree_M, tot = 0, 0, 0
    for (A, B) in pairs:
        dq = [A["q"][j] - B["q"][j] for j in range(1, 5)
              if not (np.isnan(A["q"][j]) or np.isnan(B["q"][j]))]
        if not dq:
            continue
        majority = 1 if sum(1 for t in dq if t > 0) * 2 >= len(dq) else -1
        dk = A["kstar"] - B["kstar"]
        dM = A["M"] - B["M"]
        tot += 1
        ak = (majority > 0) == (dk > 0)
        aM = (majority > 0) == (dM > 0)
        agree_k += ak
        agree_M += aM
        print(f"    n={A['n']:3d} {A['label']:>9s} vs {B['label']:9s}: "
              f"signs(dq_1..4)={fmt_signs(dq, 4)} majority={'+' if majority>0 else '-'} "
              f"dk*={dk:+.3f} dM={dM:+.3f}  predicts_k*={'Y' if ak else 'N'} "
              f"predicts_M={'Y' if aM else 'N'}")
    if tot:
        print(f"    AGGREGATE: majority-sign predicts sign(dk*) in {agree_k}/{tot} pairs "
              f"({100*agree_k/tot:.0f}%), sign(dM) in {agree_M}/{tot} "
              f"({100*agree_M/tot:.0f}%)  [50% = coin flip]")

    # ---------------- T4 spectral-shift ladder ----------------
    print("\n== T4: RITZ-EDGE / SPECTRAL-SHIFT LADDER lambda_max(J_k) ==")
    print("  one-sidedness check + increment scale at k* + gap M - lambda_max(J_ceil(k*)):")
    for r in results + controls:
        e, b, M, n = r["edges"], r["b"], r["M"], r["n"]
        mono = bool(np.all(np.diff(e) >= -1e-9 * max(1.0, M)))
        below = bool(np.all(e <= M * (1 + 1e-9)))
        kc = min(int(math.ceil(r["kstar"])), e.size - 1)
        inc_at_ks = (e[kc] - e[kc - 1]) if kc >= 1 else float("nan")
        gap = M - e[kc]
        print(f"    n={n:3d} [{r['label']:9s}] ({r['kind']}) edges monotone={mono} "
              f"all<=M={below}  incr@k*={inc_at_ks:8.4f} (={inc_at_ks/math.sqrt(n):5.2f} sqrt(n))  "
              f"gap(M - edge@ceil(k*))={gap:8.4f} (={gap/M*100:5.2f}% of M)")
    print("  cell means of relative gap at k*, real vs iid (baseline-blindness test):")
    for n in (16, 32, 64):
        def relgap(r):
            e, M = r["edges"], r["M"]
            kc = min(int(math.ceil(r["kstar"])), e.size - 1)
            return (M - e[kc]) / M
        gr = [relgap(r) for r in results if r["n"] == n]
        gi = [relgap(r) for r in controls if r["n"] == n]
        print(f"    n={n:3d}: real {np.mean(gr):.4f} +- {np.std(gr):.4f}   "
              f"iid {np.mean(gi):.4f} +- {np.std(gi):.4f}")

    # ---------------- T5 locality self-test ----------------
    print("\n== T5: window->moment locality (numeric check of the Lean brick) ==")
    worst = max(r["mom_roundtrip_relerr"] for r in results + controls)
    print(f"  worst relative error of (J_8^r)_00 vs direct moments (r <= 12, all instances): "
          f"{worst:.2e}")
    print("  (the Lean brick _W14JacobiWindowMomentEquivalence proves the exact statement:")
    print("   two symmetric tridiagonal matrices agreeing on the (K+1)x(K+1) corner have")
    print("   identical (A^r)_00 for all r <= 2K -- the window is a lossless recoding of the")
    print("   moments to order 2K, so every window/truncation invariant is a low-moment")
    print("   functional.)")

    print(f"\nTOTAL TIME {time.time()-T0:.1f}s")


if __name__ == "__main__":
    main()
