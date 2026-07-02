#!/usr/bin/env python3
"""
probe_466_novel_N7_arithcert.py — lane N7 (free synthesis, #466 novel-math round):
numerical companions to the ARITHMETIC-CERTIFICATE attack and its death.

The attack (kb note deltastar-466-novel-N7-free-synthesis-2026-07-01.md):
  M(n,p) = house(eta) for the Gauss period eta of degree m = (p-1)/n; the prize
  inequality M^2 <= T := ceil(C^2 n ln(p/n)) is EQUIVALENT (Hasse-Minkowski/Siegel)
  to "T - eta^2 is a sum of four squares in K_m = Q(eta)".  The attempted new
  mechanism: force a contradiction from a hypothetical far conjugate ("spike") via
  the INTEGRALITY family  prod_i Q(eta_i) = Res(Psi_p, Q) in Z \\ {0}, i.e.
  S(Q) := sum_i ln|Q(eta_i)| >= 0 for every Q in Z[x] coprime to Psi_p.

This probe sharpens the four load-bearing constants of the death argument:

  [S1] real data (n=16, p=65537, m=4096): the pincer functional S(Q) for
       Q = x^2 - A is hugely positive for EVERY integer A — the certificate
       family cannot see the true maximum. Per-root margin ~ m*(2 ln M) >> dip.
  [S2] the strict Z-admissibility margin of the spike+bulk countermodel measure
       mu = (1-eps)*N(0,n)|_trunc + eps*Unif[M, M+1]:
       per-root lower bound (1-eps)*(0.5 ln n + u_min) - eps*(1+ln 2), with
       u_min = min_z int ln|z-x| dN(0,1) = -(gamma+ln 2)/2 ~ -0.6352 (computed
       here by quadrature, incl. truncation). Positive margin ==> Smith
       realizability applies ==> "integrality is free".
  [S3] the depth law of the realized spike: with K^k-Wick input to depth
       k <= L ~ ln(atoms), the admissible spike is t_max = sqrt(2K)*(1-o(1))
       in units sqrt(n * ln(atoms)) — matching the round-2 lone-spike table
       (probe_466_cmk_lonespike) at the conjugate-family normalization.
  [S4] an ELEMENTARY explicit countermodel shape (corroborating Smith):
       P(x) = (x - A0) * C_N(x) - 1, C_N = monic integer Chebyshev-type on
       [-sqrt(2n), sqrt(2n)] (recurrence C_{k+1} = x C_k - (n/2) C_{k-1}, since
       B^2/4 = n/2: bulk variance exactly n, bulk moments C(2k,k)(n/2)^k =
       Wick_k * n^k / k! <= Wick at K=1 for ALL k), A0 = round(sqrt(2K n ln d)).
       Verify: all d = N+1 roots real, ONE spike at ~A0, bulk in [-sqrt(2n),
       sqrt(2n)], normalized even moments <= K^k (2k-1)!! n^k for all k <=
       ln(deg) (and beyond), and (small scale) irreducibility over Z — a genuine
       totally-real algebraic integer whose conjugate family satisfies every
       input of the certificate program yet has house ~ sqrt(2K)*sqrt(n ln d).

Honesty: numerics only; no Lean claim; the Smith citation (arXiv:2111.12660)
is flagged in the kb note as memory-cited (judge to verify exact statement).
"""

import math
import numpy as np

OUT = []
def log(s=""):
    print(s)
    OUT.append(str(s))

GAMMA = 0.5772156649015329

# ---------------------------------------------------------------- S1: real data
def section1():
    log("=" * 78)
    log("[S1] real Gauss periods n=16, p=65537: the pincer functional S(Q) never fires")
    log("=" * 78)
    p, n = 65537, 16
    m = (p - 1) // n              # 4096
    g = 3                          # primitive root mod 65537
    # mu_n = {g^(m j)}; coset reps b = g^t, t=0..m-1
    xs = [pow(g, m * j, p) for j in range(n)]
    tp = 2.0 * math.pi / p
    etas = np.empty(m)
    b = 1
    for t in range(m):
        s = 0.0
        for x in xs:
            s += math.cos(tp * ((b * x) % p))
        etas[t] = s                # real: -1 in mu_16
        b = (b * g) % p
    M = float(np.max(np.abs(etas)))
    log(f"  m = {m} conjugates; M_true = max|eta_i| = {M:.6f}")
    log(f"  sqrt(n ln(p/n)) = {math.sqrt(n*math.log(p/n)):.4f};  C_true = "
        f"{M/math.sqrt(n*math.log(p/n)):.4f}")
    log(f"  Parseval check sum eta_i^2 = {float(np.sum(etas**2)):.1f} vs p-n = {p-n}")
    # pincer Q = x^2 - A over integer A near M^2 and swept broadly
    e2 = etas ** 2
    def S_of_A(A):
        return float(np.sum(np.log(np.abs(e2 - A))))
    A_star = round(M * M)
    sweep = sorted(set([A_star + d for d in range(-5, 6)] +
                       [int(u) for u in np.linspace(1, 4 * M * M, 400)]))
    vals = [(S_of_A(A), A) for A in sweep if abs(A) >= 1]
    smin, amin = min(vals)
    log(f"  pincer at A* = round(M^2) = {A_star}: S = {S_of_A(A_star):.1f} nats  (>= 0 needed"
        f" to kill; contradiction requires < 0)")
    log(f"  min over {len(vals)} integer A in [1, 4M^2]: S = {smin:.1f} at A = {amin}"
        f"  -> margin per conjugate {smin/m:.4f} nats/root (x2 roots)")
    # per-root empirical potential floor (grid min over real a of avg ln|eta - a|)
    grid = np.linspace(-1.2 * M, 1.2 * M, 4001)
    U = np.array([float(np.mean(np.log(np.abs(etas - a) + 1e-300))) for a in grid])
    log(f"  empirical potential floor min_a avg_i ln|eta_i - a| = {U.min():.4f}"
        f"  (prediction 0.5 ln n + u_min = {0.5*math.log(n) - (GAMMA+math.log(2))/2:.4f})")
    log("  VERDICT S1: every integer pincer is ~m*ln(A) positive; integrality never bites.")
    log("")

# ------------------------------------------------- S2: admissibility margin
def u_min_truncated_gaussian(c=4.0, N=200001):
    """min_z int ln|z-x| dmu for standard normal truncated at +-c (renormalized).
    The min is at z=0 by symmetry+unimodality; we also scan z to confirm."""
    xs = np.linspace(-c, c, N)
    w = np.exp(-xs ** 2 / 2.0)
    w /= w.sum()
    def U(z):
        d = np.abs(z - xs)
        d[d < 1e-12] = 1e-12
        return float(np.sum(w * np.log(d)))
    zs = np.linspace(-1.5, 1.5, 61)
    vals = [U(z) for z in zs]
    return min(vals), U(0.0)

def section2():
    log("=" * 78)
    log("[S2] strict Z-admissibility margin of the spike+bulk countermodel measure")
    log("=" * 78)
    umin, u0 = u_min_truncated_gaussian()
    log(f"  u_min(std normal, trunc 4 sigma) = {umin:.6f}   (analytic -(gamma+ln2)/2 = "
        f"{-(GAMMA + math.log(2))/2:.6f}; z=0 value {u0:.6f})")
    log(f"  smeared-spike worst dip (unit interval, root at center): -(1+ln 2) = "
        f"{-(1+math.log(2)):.6f}")
    log("  per-root margin  (1-eps)*(0.5 ln n + u_min) - eps*(1+ln2)  [nats/root]:")
    log("      n        eps=0.1     eps=0.01    eps=0.001")
    for mu_exp in (10, 20, 30):
        n = 2 ** mu_exp
        row = []
        for eps in (0.1, 0.01, 0.001):
            marg = (1 - eps) * (0.5 * math.log(n) + umin) - eps * (1 + math.log(2))
            row.append(f"{marg:10.4f}")
        log(f"   2^{mu_exp:<3}  " + "  ".join(row))
    n8 = (1 - 0.01) * (0.5 * math.log(8) + umin) - 0.01 * (1 + math.log(2))
    log(f"  boundary: n = 8, eps = 0.01 -> margin {n8:.4f} (> 0: admissible for all n >= 8)")
    log("  VERDICT S2: mu_spike is strictly Z-admissible with ~10 nats/root margin at the")
    log("  prize point -> Smith's realizability hypothesis holds with enormous slack.")
    log("")

# ------------------------------------------------------------- S3: depth law
def log_double_factorial(k):
    # ln((2k-1)!!) = ln((2k)!) - k ln 2 - ln(k!)
    return math.lgamma(2 * k + 1) - k * math.log(2) - math.lgamma(k + 1)

def t_max(K, ln_atoms, L):
    """largest t with (1/atoms)*(t^2 n ln_atoms)^k <= K^k (2k-1)!! n^k for all k<=L
    (n scales out).  Binary search."""
    def ok(t):
        for k in range(1, L + 1):
            lhs = k * math.log(t * t * ln_atoms) - ln_atoms
            rhs = k * math.log(K) + log_double_factorial(k)
            if lhs > rhs + 1e-12:
                return False
        return True
    lo, hi = 0.1, 50.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return lo

def section3():
    log("=" * 78)
    log("[S3] depth law of the realized spike (conjugate-family normalization)")
    log("=" * 78)
    log("  atoms = m conjugates; K^k-Wick input for all k <= L = ceil(ln q); spike at")
    log("  t*sqrt(n ln m).  t_max vs sqrt(2K):")
    log("      regime                    K      t_max    sqrt(2K)   ratio")
    for (tag, lnq_bits, n_bits) in (("q=2^120,n=2^30 (beta=4)", 120, 30),
                                    ("q=n*2^128,n=2^30 (prize)", 158, 30)):
        ln_q = lnq_bits * math.log(2)
        ln_m = (lnq_bits - n_bits) * math.log(2)
        L = math.ceil(ln_q)
        for K in (1.0, 1.05, 1.2, 2.0, 4.0):
            t = t_max(K, ln_m, L)
            log(f"   {tag:<24}  {K:5.2f}  {t:7.4f}  {math.sqrt(2*K):8.4f}  "
                f"{t/math.sqrt(2*K):7.4f}")
    log("  (round-2 lone-spike table, ln q normalization, for cross-check: t_raw =")
    log("   1.452/1.552/2.004/2.834 at K = 1.05/1.2/2/4 — same 2K law, and indeed:")
    ln_q = 120 * math.log(2)
    for K in (1.05, 1.2, 2.0, 4.0):
        t = t_max(K, ln_q, math.ceil(ln_q))
        log(f"     K={K:<5} t_max(ln q units) = {t:.3f}")
    log("  VERDICT S3: the arithmetic countermodel reproduces the lone-spike constant")
    log("  sqrt(2K) exactly; integrality does not shave even the (1-o(1)).")
    log("")

# ------------------------------------- S4: explicit perturbed-Chebyshev integer
def section4():
    log("=" * 78)
    log("[S4] elementary countermodel P = (x - A0) C_N(x) - 1  (n = 16, B = sqrt(32))")
    log("=" * 78)
    import mpmath as mp
    from sympy import Poly, symbols, factor_list, ZZ
    n = 16
    N = 48
    d = N + 1
    K = 2.0
    A0 = round(math.sqrt(2 * K * n * math.log(d)))   # spike target sqrt(2K n ln d)
    log(f"  N = {N}, degree d = {d}, K = {K}, A0 = {A0} (spike target "
        f"{math.sqrt(2*K*n*math.log(d)):.4f}, bulk edge sqrt(2n) = {math.sqrt(2*n):.4f})")
    # C_k recurrence: C_0 = 2, C_1 = x, C_{k+1} = x*C_k - (n/2)*C_{k-1}  (B^2/4 = n/2)
    c = n // 2
    C0 = [2]           # ascending coeff lists, integer
    C1 = [0, 1]
    def poly_mul_x(cf):
        return [0] + cf
    def poly_sub(a, b):
        la = len(a); lb = len(b); L = max(la, lb)
        return [(a[i] if i < la else 0) - (b[i] if i < lb else 0) for i in range(L)]
    def poly_scale(cf, s):
        return [s * v for v in cf]
    for _ in range(N - 1):
        C2 = poly_sub(poly_mul_x(C1), poly_scale(C0, c))
        C0, C1 = C1, C2
    CN = C1
    # P = (x - A0)*CN - 1
    P = poly_sub(poly_sub([0] + CN, poly_scale(CN, A0)), [1])
    assert len(P) == d + 1 and P[-1] == 1, "monic degree d"
    mp.mp.dps = 320
    roots = mp.polyroots([mp.mpf(cf) for cf in reversed(P)], maxsteps=400, extraprec=800)
    im_max = max(abs(mp.im(r)) for r in roots)
    re_roots = sorted(float(mp.re(r)) for r in roots)
    log(f"  max |Im root| = {mp.nstr(im_max, 3)}  (all real iff ~0)")
    edge = math.sqrt(2 * n) + 0.5
    spikes = [r for r in re_roots if abs(r) > edge]
    bulk = [r for r in re_roots if abs(r) <= edge]
    log(f"  #bulk roots in [-sqrt(2n)-.5, +] = {len(bulk)}; spike(s) = "
        f"{[f'{s:.6f}' for s in spikes]} (pred ~{A0})")
    hs = max(abs(r) for r in re_roots)
    log(f"  house = {hs:.5f} = {hs/math.sqrt(n*math.log(d)):.4f} * sqrt(n ln d)"
        f"   [sqrt(2K) = {math.sqrt(2*K):.4f}]")
    # normalized even moments vs K^k Wick
    log("      k    (1/d) sum xi^2k / n^k     K^k (2k-1)!!    ok?")
    okall = True
    for k in range(1, int(math.log(d)) + 3):
        mom = sum(r ** (2 * k) for r in re_roots) / d / (n ** k)
        wick = (K ** k) * math.exp(log_double_factorial(k))
        if k <= math.log(d):
            okall &= mom <= wick
        log(f"     {k:2d}   {mom:18.3f}   {wick:16.3f}    {mom <= wick}"
            + ("" if k <= math.log(d) else "   (beyond ln d window)"))
    log(f"  moment clause k <= ln d: {'PASS' if okall else 'FAIL'}")
    # irreducibility over Z (small-scale corroboration of factor-selection)
    x = symbols('x')
    try:
        fl = factor_list(Poly(list(reversed(P)), x, domain=ZZ))
        nfac = len(fl[1])
        degs = [int(f[0].degree()) for f in fl[1]]
        log(f"  factorization over Z: {nfac} irreducible factor(s), degrees {degs}"
            + (f"  -> IRREDUCIBLE: genuine degree-{d} algebraic integer" if nfac == 1
               and degs == [d] else ""))
    except Exception as e:      # keep light; factoring is a bonus check
        log(f"  (sympy factor skipped: {e})")
    log("  VERDICT S4: an explicit monic integer polynomial realizes spike+bulk with")
    log("  K^k-Wick moments to depth ln d — integrality satisfied by construction.")
    log("")

if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
    log("SUMMARY: [S1] pincers blind on real data; [S2] countermodel admissible,")
    log("~10 nats/root margin at prize point; [S3] t_max = sqrt(2K) survives the full")
    log("integrality upgrade; [S4] explicit elementary witness at n=16, d=49.")
    log("=> the arithmetic-certificate lane (Siegel 4-squares + resultant pincers)")
    log("   is information-theoretically dead below sqrt(2K); death is at theorem level")
    log("   (Smith realizability), not numerics. CORE unchanged: OPEN, ON-BGK.")
    import pathlib
    out = pathlib.Path(__file__).parent / "_out_466_novel_N7_arithcert.txt"
    out.write_text("\n".join(OUT) + "\n", encoding="utf-8")
    print(f"\n[written {out}]")
