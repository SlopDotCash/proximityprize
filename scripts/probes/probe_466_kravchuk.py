#!/usr/bin/env python3
"""
probe_466_kravchuk.py -- LANE P3: Kravchuk moment-interlacing probe.
Issue #466; dossier v3 (docs/kb/deltastar-DOSSIER-v3-2026-07-01.md) sec 6 Tier-2:
  "Kravchuk moment-interlacing numerical check (SCL_rho vs 1-sqrt(rho); risk: re-derives Johnson)".

CLAIM UNDER TEST (2604.09533-style): "MDS forces the agreement-count distribution to share its
first moments with Binomial(m,1/2) regardless of evaluation set, so the max agreement is pinned
by the largest Kravchuk root (semicircle law), evaluation-point-independent."

WHAT THIS PROBE COMPUTES
(a) Largest root x_max of the degree-k Kravchuk polynomial K_k^{(m)} over {0..m}
    (orthogonal wrt Binomial(m,1/2)), m = n, k = rho*n,
    rho in {1/2, 1/4, 1/8, 1/16}, n in {64,128,256,512} (+ 1024/2048/4096 convergence check).
    Two candidate normalizations of the implied max-agreement fraction:
       SCL_A = x_max / m            (literal "agreement pinned at the largest root")
       SCL_B = (x_max - m/2) / m    (excess-over-random-baseline m/2 reading)
    Known analytic limits (Levenshtein extreme-zero asymptotics, numerically confirmed here):
       SCL_A -> 1/2 + sqrt(rho(1-rho)),   SCL_B -> sqrt(rho(1-rho)).
(b) Compare against Johnson agreement sqrt(rho) (radius 1-sqrt(rho)) and capacity rho.
(c) DIRECTION + ALPHABET AUDITS (the honest part):
    - The moment premise is TRUE and evaluation-set-independent: for an [m,k] MDS code over F_q,
      coordinates of a uniform codeword are k-wise independent uniform, so for ANY word y the
      agreement count A(y,c) satisfies the exact factorial-moment identity
          sum_{c in C} C(A(y,c), r) = C(m,r) * q^{k-r}   for all r <= k
      (= Binomial(m,1/q) factorial moments; note 1/q, NOT 1/2).  Verified exactly (integer
      arithmetic) on RS codes for 2 primes x 2 lengths x 2 evaluation sets.
    - COUNTERMODEL to the "pin": take y IN the code. Same first-k moments, but
      max_c A(y,c) = m >> any Kravchuk root.  Moment matching pins the max only from BELOW
      (Gauss-quadrature: first 2t-1 moments matching => max support >= largest root of the
      degree-t orthogonal polynomial); it is NOT an upper bound.
    - Honest RS weight is Binomial(m,1/q): its largest root sits far BELOW capacity rho*m and
      below the guaranteed pairwise codeword agreement k-1 -- so the "upper bound" reading is
      falsified inside the code itself for every RS alphabet.
    - Binomial(m,1/2) has no nontrivial MDS instance: binary MDS codes are only the trivial
      [m,1], [m,m-1], [m,m].

DECISION RULE (from lane brief):
  SCL -> sqrt(rho) for every rate  => REFUTED (re-derives Johnson; joins second-order cap).
  SCL strictly between rho and sqrt(rho) with stable gap => LIVE (only if it is a valid bound!).
"""

import numpy as np
from math import comb, sqrt, ceil
from fractions import Fraction

try:
    from scipy.linalg import eigh_tridiagonal
    HAVE_SCIPY = True
except ImportError:
    HAVE_SCIPY = False

RNG = np.random.default_rng(466)


# ----------------------------------------------------------------------------
# Kravchuk extreme roots via Jacobi (Golub-Welsch) matrix.
# Monic Krawtchouk wrt Binomial(m,p):  alpha_j = m p + j(1-2p),  beta_j = j p(1-p)(m-j+1).
# Sanity anchors: t=1 root = mp;  t=2 (p=1/2) roots = (m +- sqrt(m))/2.
# ----------------------------------------------------------------------------
def kraw_extreme_roots(m, t, p=0.5):
    if t < 1:
        raise ValueError("degree must be >= 1")
    j = np.arange(t, dtype=float)
    diag = m * p + j * (1.0 - 2.0 * p)
    if t == 1:
        return float(diag[0]), float(diag[0])
    jj = np.arange(1, t, dtype=float)
    off = np.sqrt(jj * p * (1.0 - p) * (m - jj + 1.0))
    if HAVE_SCIPY:
        w = eigh_tridiagonal(diag, off, eigvals_only=True)
    else:
        A = np.diag(diag) + np.diag(off, 1) + np.diag(off, -1)
        w = np.linalg.eigvalsh(A)
    return float(w[0]), float(w[-1])


# Cross-check: evaluate binary Kravchuk by the stable 3-term recurrence
# (j+1) K_{j+1}(x) = (m-2x) K_j(x) - (m-j+1) K_{j-1}(x),  K_0=1, K_1=m-2x.
def K_eval_half(m, k, x):
    x = np.asarray(x, dtype=float)
    Km1 = np.zeros_like(x)
    K0 = np.ones_like(x)
    for j in range(k):
        K1 = ((m - 2.0 * x) * K0 - (m - j + 1.0) * Km1) / (j + 1.0)
        Km1, K0 = K0, K1
    return K0


def largest_root_direct(m, k, grid=200001):
    xs = np.linspace(0.0, float(m), grid)
    vals = K_eval_half(m, k, xs)
    s = np.sign(vals)
    idx = np.nonzero(s[:-1] * s[1:] < 0)[0]
    assert len(idx) == k, f"expected {k} sign changes, got {len(idx)} (m={m},k={k})"
    lo, hi = xs[idx[-1]], xs[idx[-1] + 1]
    flo = K_eval_half(m, k, np.array([lo]))[0]
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        fmid = K_eval_half(m, k, np.array([mid]))[0]
        if flo * fmid <= 0:
            hi = mid
        else:
            lo, flo = mid, fmid
    return 0.5 * (lo + hi)


def extrapolate_edge(ms, vals):
    """Fit vals ~ a + b*m^(-2/3) (extreme-zero edge rate) by least squares; return a."""
    X = np.vstack([np.ones(len(ms)), np.asarray(ms, float) ** (-2.0 / 3.0)]).T
    coef, *_ = np.linalg.lstsq(X, np.asarray(vals, float), rcond=None)
    return float(coef[0])


# ----------------------------------------------------------------------------
# RS agreement-count audit: exact factorial moments + max agreement.
# ----------------------------------------------------------------------------
def rs_codewords(q, m, k, eval_pts):
    """All q^k RS codewords (degree<k polys) evaluated at eval_pts. Returns (q^k, m) int array."""
    xs = np.asarray(eval_pts, dtype=np.int64)
    assert len(set(xs.tolist())) == m and m <= q
    V = np.empty((m, k), dtype=np.int64)
    for i in range(m):
        for j in range(k):
            V[i, j] = pow(int(xs[i]) % q, j, q)
    # enumerate all coefficient tuples
    grids = np.indices((q,) * k).reshape(k, -1).T  # (q^k, k)
    return (grids @ V.T) % q


def factorial_moment_audit(q, m, k, eval_pts, y, words):
    """Check sum_c C(A(y,c),r) == C(m,r) q^{k-r} exactly for r=1..k; return (ok, maxA, A)."""
    A = (words == np.asarray(y, dtype=np.int64)[None, :]).sum(axis=1)
    ok = True
    for r in range(1, k + 1):
        S = sum(comb(int(a), r) for a in A)
        expected = comb(m, r) * q ** (k - r)
        if S != expected:
            ok = False
            print(f"      MOMENT MISMATCH r={r}: sum C(A,r)={S} vs C(m,r)q^(k-r)={expected}")
    return ok, int(A.max()), A


# ----------------------------------------------------------------------------
def main():
    import scipy
    print("=" * 100)
    print("PROBE 466 / LANE P3: Kravchuk moment-interlacing vs Johnson")
    print(f"numpy {np.__version__}, scipy {scipy.__version__ if HAVE_SCIPY else 'ABSENT (dense fallback)'}")
    print("=" * 100)

    # ---------------- sanity cross-checks -------------------------------------
    print("\n[0] SANITY: Jacobi-matrix roots vs direct polynomial roots (p=1/2)")
    worst = 0.0
    for (m, k) in [(16, 4), (32, 8), (64, 8), (64, 16)]:
        xmin, xmax = kraw_extreme_roots(m, k, 0.5)
        direct = largest_root_direct(m, k)
        err = abs(xmax - direct)
        worst = max(worst, err)
        sym = abs((xmin + xmax) - m)  # p=1/2 roots symmetric about m/2
        print(f"    m={m:3d} k={k:3d}: eig x_max={xmax:.8f}  direct={direct:.8f}  |diff|={err:.2e}  symmetry|x_min+x_max-m|={sym:.2e}")
        assert err < 1e-6 and sym < 1e-8
    # closed-form t=2 anchor: roots (m +- sqrt(m))/2
    xmin2, xmax2 = kraw_extreme_roots(100, 2, 0.5)
    assert abs(xmax2 - (100 + sqrt(100)) / 2) < 1e-10
    print(f"    t=2 anchor m=100: x_max={xmax2:.6f} == (m+sqrt(m))/2 OK   (worst cross-check err {worst:.2e})")

    # ---------------- (a)+(b): the main table ---------------------------------
    rates = [Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 16)]
    ns_main = [64, 128, 256, 512]
    ns_ext = [1024, 2048, 4096]
    ns_all = ns_main + ns_ext

    print("\n[1] LARGEST KRAVCHUK ROOT, p=1/2, degree k=rho*n over {0..m}, m=n")
    print("    SCL_A = x_max/m (literal root agreement);  SCL_B = (x_max-m/2)/m (excess reading)")
    print("    semicircle limits: SCL_A -> 1/2+sqrt(rho(1-rho)),  SCL_B -> sqrt(rho(1-rho))")
    summary = {}
    for rho in rates:
        rf = float(rho)
        limA = 0.5 + sqrt(rf * (1 - rf))
        limB = sqrt(rf * (1 - rf))
        print(f"\n  rate rho={rho}  (Johnson sqrt(rho)={sqrt(rf):.6f}, capacity rho={rf:.6f})")
        print(f"    {'n':>5} {'k':>5} {'x_max':>12} {'SCL_A=x/m':>11} {'SCL_B=(x-m/2)/m':>16} {'gap_to_semicircle_A':>20}")
        msA, msB, ms = [], [], []
        for n in ns_all:
            k = int(rho * n)
            _, xmax = kraw_extreme_roots(n, k, 0.5)
            sclA = xmax / n
            sclB = (xmax - n / 2) / n
            ms.append(n); msA.append(sclA); msB.append(sclB)
            tag = "" if n in ns_main else "  (conv-check)"
            print(f"    {n:>5} {k:>5} {xmax:12.4f} {sclA:11.6f} {sclB:16.6f} {limA - sclA:20.6f}{tag}")
        extA = extrapolate_edge(ms[-4:], msA[-4:])
        extB = extrapolate_edge(ms[-4:], msB[-4:])
        print(f"    m^(-2/3)-extrapolated:  SCL_A_inf={extA:.6f} (semicircle {limA:.6f}),  "
              f"SCL_B_inf={extB:.6f} (semicircle {limB:.6f})")
        summary[rho] = dict(extA=extA, extB=extB, limA=limA, limB=limB,
                            johnson=sqrt(rf), capacity=rf,
                            gap_trendA=[abs(a - limA) for a in msA],
                            seqB=msB, seqA=msA)

    # honest quadrature degree: k matched moments only support Gauss quadrature at t=ceil(k/2)
    print("\n[1b] HONEST QUADRATURE DEGREE t=ceil(k/2) (k moments => degree-t largest root is the")
    print("     max-agreement LOWER bound; limit SCL_B -> sqrt((rho/2)(1-rho/2)) )")
    for rho in rates:
        rf = float(rho)
        n = 4096
        k = int(rho * n)
        t = ceil(k / 2)
        _, xmax = kraw_extreme_roots(n, t, 0.5)
        lim = sqrt((rf / 2) * (1 - rf / 2))
        print(f"    rho={rho}: n={n} t={t}: SCL_A={xmax/n:.6f}  SCL_B={(xmax-n/2)/n:.6f}  (limit_B {lim:.6f})"
              f"   vs Johnson {sqrt(rf):.4f}, capacity {rf:.4f}")

    # ---------------- (b): decision-rule comparison ----------------------------
    print("\n[2] DECISION-RULE COMPARISON (extrapolated limits vs Johnson sqrt(rho) vs capacity rho)")
    print(f"    {'rho':>6} {'SCL_A_inf':>10} {'SCL_B_inf':>10} {'sqrt(rho)':>10} {'rho':>8}"
          f" {'A vs Johnson':>14} {'B vs Johnson':>14} {'B/sqrt(rho)':>12}")
    for rho, d in summary.items():
        rf = float(rho)
        posA = "ABOVE" if d["extA"] > d["johnson"] + 1e-3 else ("=Johnson" if abs(d["extA"] - d["johnson"]) < 1e-3 else "below")
        posB = "between" if d["capacity"] + 1e-3 < d["extB"] < d["johnson"] - 1e-3 else \
               ("=capacity" if abs(d["extB"] - d["capacity"]) < 1e-3 else
                ("=Johnson" if abs(d["extB"] - d["johnson"]) < 1e-3 else "other"))
        print(f"    {str(rho):>6} {d['extA']:10.6f} {d['extB']:10.6f} {d['johnson']:10.6f} {rf:8.4f}"
              f" {posA:>14} {posB:>14} {d['extB']/d['johnson']:12.6f}")
    print("    note: SCL_B/sqrt(rho) -> sqrt(1-rho) -> 1 as rho->0  (Johnson re-derivation in the")
    print("    small-rate limit; the sqrt(1-rho) 'gain' is dissected in [3]/[4] below)")

    # ---------------- (c): moment premise + countermodel -----------------------
    print("\n[3] EXACT MOMENT AUDIT ON RS CODES (2 primes x 2 lengths x 2 evaluation sets)")
    print("    identity: sum_c C(A(y,c),r) = C(m,r) q^(k-r), r<=k  ( = Binomial(m,1/q) factorial")
    print("    moments, NOT Binomial(m,1/2) )  -- checked in exact integer arithmetic")
    cases = [(13, 8, 3), (17, 8, 3), (13, 12, 3), (17, 12, 3)]
    all_ok = True
    for (q, m, k) in cases:
        for tag, pts in [("consecutive", list(range(m))),
                         ("random", sorted(RNG.choice(q, size=m, replace=False).tolist()))]:
            words = rs_codewords(q, m, k, pts)
            # y = a codeword (the zero word)
            y_in = np.zeros(m, dtype=np.int64)
            ok1, max_in, _ = factorial_moment_audit(q, m, k, pts, y_in, words)
            # y = a non-codeword (verify it is one)
            while True:
                y_out = RNG.integers(0, q, size=m)
                A = (words == y_out[None, :]).sum(axis=1)
                if A.max() < m:
                    break
            ok2, max_out, _ = factorial_moment_audit(q, m, k, pts, y_out, words)
            t = ceil(k / 2)
            _, root = kraw_extreme_roots(m, t, 1.0 / q)
            _, rootk = kraw_extreme_roots(m, k, 1.0 / q)
            all_ok = all_ok and ok1 and ok2
            print(f"    q={q:2d} m={m:2d} k={k} eval={tag:11s}: moments {'EXACT' if ok1 and ok2 else 'FAIL'}"
                  f" (both y);  max A: y-in-code={max_in} (=m: {max_in==m}), y-outside={max_out};"
                  f"  Kravchuk_(1/q) root: deg-{t}={root:.3f}, deg-{k}={rootk:.3f};  pairwise agreement k-1={k-1}")
    print(f"    => moment premise TRUE + evaluation-set-independent: {all_ok}")
    print("    => COUNTERMODEL: y in code has the SAME first-k moments but max agreement = m,")
    print("       far above every Kravchuk root => largest root is NOT an upper bound ('pin' false);")
    print("       Gauss quadrature makes it a LOWER bound on max agreement only.")

    # ---------------- honest alphabet: p = 1/q at prize-like scales -------------
    print("\n[4] HONEST WEIGHT Binomial(m,1/q) AT SCALE (no in-window content either way)")
    print("    deg-k root/m -> (sqrt(rho(1-p))+sqrt(p(1-rho)))^2 -> rho as q->inf: full-degree")
    print("    semicircle at the honest weight reproduces the TRIVIAL degree bound k (capacity),")
    print("    not sqrt(rho); the moment-budget-justified degree t=ceil(k/2) root sits near rho/2")
    print("    (a weak covering-type LOWER bound). Neither reading touches Johnson.")
    for q in [257, 65537]:
        for n in [64, 256]:
            for rho in [Fraction(1, 2), Fraction(1, 8)]:
                k = int(rho * n)
                t = ceil(k / 2)
                _, rt = kraw_extreme_roots(n, t, 1.0 / q)
                _, rk = kraw_extreme_roots(n, k, 1.0 / q)
                print(f"    q={q:5d} n={n:3d} rho={str(rho):4s}: deg-{k} root/m={rk/n:.4f} (~capacity {float(rho):.4f}),"
                      f" deg-{t} root/m={rt/n:.4f} (~rho/2={float(rho)/2:.4f});"
                      f" pairwise (k-1)/m={(k-1)/n:.4f}")
    print("    (a received word equal to a codeword has agreement m with matching first-k moments,")
    print("     so no root is an upper bound; as a lower bound the honest-degree root ~rho/2 is a")
    print("     covering-type statement with no list-decoding content)")

    # ---------------- verdict ---------------------------------------------------
    print("\n" + "=" * 100)
    print("VERDICT: REFUTED (no in-window bound; the live-looking reading is direction-invalid)")
    print("=" * 100)
    for rho, d in summary.items():
        print(f"  rho={str(rho):4s}: SCL_A={d['extA']:.4f} > Johnson {d['johnson']:.4f} (WEAKER than Johnson);"
              f"  SCL_B={d['extB']:.4f} = sqrt(rho(1-rho)) = Johnson*sqrt(1-rho)")
    print("""
  (i)  Literal reading (SCL_A = x_max/m -> 1/2+sqrt(rho(1-rho))): strictly ABOVE Johnson agreement
       sqrt(rho) at every prize rate -- the semicircle 'pin' is weaker than Johnson in-window.
  (ii) Excess reading (SCL_B -> sqrt(rho(1-rho)) = sqrt(rho)sqrt(1-rho)): lands numerically between
       capacity and Johnson for rho<=1/4, BUT it is not a valid upper bound: (a) exact countermodel
       in [3] (same first-k moments, max agreement = m); moment interlacing bounds the max from
       BELOW (quadrature), never from above; (b) the Binomial(m,1/2) premise has no nontrivial MDS
       instance (q=2 MDS is trivial) -- at the honest RS weight Binomial(m,1/q) the full-degree
       root collapses to capacity (= the trivial degree bound) and the moment-budget-justified
       degree-ceil(k/2) root to ~rho/2, a covering-type lower bound ([4]).
  (iii) Evaluation-point-independence is REAL but is exactly the second-order-cap signature: the
       premise (k-wise independence) holds for every evaluation set, hence cannot see mu_n and
       cannot certify any delta* beyond the universal (Johnson) surface.
  Dossier risk 'merely re-derives Johnson' CONFIRMED in the rho->0 limit (SCL_B/sqrt(rho) =
  sqrt(1-rho) -> 1); at prize rates it is Johnson-or-weaker in every valid reading.
""")


if __name__ == "__main__":
    main()
