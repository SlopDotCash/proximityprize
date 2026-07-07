"""probe_466_cmk_lonespike.py -- LANE R1 (#466): decide Conjecture CMK (essay
docs/kb/deltastar-466-essay-novel-mathematics-2026-07-01.md sec 2.2).

CMK (as stated): for measures with q-1 EQUAL atoms (mass 1/(q-1) each),
Parseval second moment ~ n (exactly n(q-n)/(q-1) in the arithmetic model),
and all even moments within factor K^r of Wick-Hermite ((2r-1)!! n^r) to
depth 2j = 2*ceil(log q)  [natural log; the essay uses q^(1/2j) ~ sqrt(e)],
the largest atom obeys M^2 <= C(K) * n * log q -- with Christoffel-function /
edge-crowding rigidity IMPROVING on the raw moment bound.

RAW MOMENT BOUND (form A, at the same data): the extreme atom has mass exactly
1/(q-1), so M^{2r}/(q-1) <= m_{2r} <= K^r (2r-1)!! n^r for every r <= j, hence
    t_raw(K)^2 := M^2/(n ln q) <= min_{r<=j} K * [(q-1)(2r-1)!!]^{1/r} / ln q
                = 2K (1+o(1))   (optimum at r ~ ln q, interior).
(The lane prompt's "~sqrt(2e)" is the un-optimized Stirling version
[(2r-1)!!]^{1/2r} ~ sqrt(2r) WITHOUT the /e; the exact optimized constant is
sqrt(2K).  We print both.)

ATTACK: lone-spike countermodel.  Measure = one atom at M = t*sqrt(n ln q)
plus (q-2) equal atoms at midpoint-Gaussian-quantile positions sigma*x_i,
x_i = Phi^{-1}((i-1/2)/(q-2)), sigma chosen so the TOTAL second moment equals
the Parseval value n(q-n)/(q-1) EXACTLY.  All masses exactly 1/(q-1).
Question: how large can t be while all even moments to depth 2j stay within
K^r of Wick?  If t_spike(K) ~= t_raw(K), the abstract problem's answer IS the
moment bound and CMK-as-improvement is REFUTED.

NUMERICAL RIGOR (the flagged trap = bulk-quantile edge effects):
the bulk moment  c_{2r} = (1/(q-2)) sum_i x_i^{2r}  is computed with a
CERTIFIED two-sided bracket:
  * top T = 2e5 extreme atoms summed exactly (scipy isf, double precision;
    rel err ~ 2r * 1e-16 <~ 1e-13, far below bracket widths reported);
  * the remaining central atoms: g(v) = Phi^{-1}(1-v)^{2r} is decreasing in
    the upper-tail probability v, and for decreasing g the midpoint sum obeys
      int_{v_i}^{v_i+h} g <= h g(v_i) <= int_{v_i-h}^{v_i} g ,
    which telescopes to sandwich the central sum between two shifted integrals
      int_0^{x(a)} x^{2r} phi(x) dx = ((2r-1)!!/2) * P(r+1/2, x(a)^2/2)
    (P = regularized lower incomplete gamma, mpmath), evaluated at
    a = (T +/- 1/2)h.  So beta_r := c_{2r}/(2r-1)!! gets a rigorous [lo,hi].
  * VALIDATION: at q = 2^24 the full sum over all 16,777,214 atoms is
    enumerated directly and checked to lie inside the bracket, with a
    documented relative tolerance 1e-11 for the double-precision top-atom
    sums (both sides use scipy isf floats; at r where the bracket width is
    dominated by that float error the strict interval test is meaningless).

Everything is scale-invariant in n: with unit-variance bulk and spike at
t*sqrt(ln q), the moment/Wick ratios depend only on q (= n^4 => ln q = 4 ln n).

ALSO SETTLED HERE:
  1. bulk moment error quantified: beta_r = P(r+1/2, x_max^2/2) + O(bracket),
     x_max = Phi^{-1}(1 - 1/(2(q-2))): tail-truncation UNDERSHOOT, ~0.3-0.5
     at r = ceil(ln q) (i.e. K_bulk = (1/beta_L)^{1/L} -> 1), ~q^{-c} at
     r = 2 ln q (K_bulk ~ 1.1-1.3 there).  Two-sidedness is therefore free at
     the CMK-stated depth and cheap even at doubled depth.
  2. the essay's "improved constant" Christoffel-with-Hermite claim: we
     compute the EXACT orthonormal-Hermite kernel threshold
        t*_H(q) = min{ t : K^Herm_j(t sqrt(ln q)) > q-1 },  j = ceil(ln q).
     Computed values: 1.385 / 1.391 / 1.395 / 1.400 at q = 2^40..2^120,
     rising slowly toward sqrt(2) FROM BELOW.  Explanation: for x inside the
     oscillatory region (x < sqrt(2j), i.e. t < sqrt(2)) the kernel obeys
     K^H_j(x,x) ~ C e^{x^2/2} sqrt(2j - x^2)  (density-of-states amplitude),
     so K^H_j = q first at x^2/2 = ln q - O(log log q), i.e.
     t*_H = sqrt(2)(1 - O(log log q / log q)).  The Hermite-substituted
     Christoffel bound therefore REPRODUCES the raw moment bound constant
     sqrt(2); it does not improve it.  The essay's "t <= 1" came from the
     leading-term substitution He_j(M) ~ M^j, which is invalid at
     M ~ sqrt(2j) (it needs M >> j) -- a computational error.
  3. true-kernel self-consistency at small scale: for the countermodel itself
     (q-1 = 10001 atoms), the Christoffel bound mass <= 1/K_j(M,M) is
     satisfied AUTOMATICALLY (the spike deforms its own orthogonal
     polynomials; one atom absorbs one quadrature node), while the Hermite
     PROXY kernel at the same point exceeds q-1.  "Edge crowding" never
     fires: the spike has zero near neighbors and all constraints hold.

Output: scripts/probes/_out_466_cmk_lonespike.txt
"""

import numpy as np
from scipy.stats import norm
from scipy.special import gammaln, logsumexp
import mpmath as mp

mp.mp.dps = 50
LN2 = float(np.log(2.0))


def logdf(r):
    """log (2r-1)!! = log( (2r)! / (2^r r!) )"""
    return gammaln(2 * r + 1) - r * np.log(2.0) - gammaln(r + 1)


def regP(a, z):
    """regularized lower incomplete gamma P(a,z)"""
    return float(mp.gammainc(mp.mpf(a), 0, mp.mpf(z), regularized=True))


# ----------------------------------------------------------------------
# certified brackets for the unit-variance quantile bulk
# ----------------------------------------------------------------------
def bulk_brackets(q, rmax, T=200000):
    """beta_r = c_{2r}/(2r-1)!!  for the midpoint-quantile atomization of
    N(0,1) with N = q-2 atoms.  Returns (lo, hi) arrays, index r=0..rmax,
    certified up to the stated double-precision top-atom error."""
    N = q - 2.0
    h = 1.0 / N
    i = np.arange(1, T + 1, dtype=np.float64)
    v = (i - 0.5) * h
    x = norm.isf(v)                      # top-T atom positions (positive tail)
    lnx = np.log(x)
    lnN = np.log(N)
    xa_lo = norm.isf((T + 0.5) * h)      # boundary for LOWER middle integral
    xa_hi = norm.isf((T - 0.5) * h)      # boundary for UPPER middle integral
    lo = np.ones(rmax + 1)
    hi = np.ones(rmax + 1)
    for r in range(1, rmax + 1):
        ltop = logsumexp(2 * r * lnx) + np.log(2.0) - lnN - logdf(r)
        top = float(np.exp(ltop))
        Plo = regP(r + 0.5, xa_lo ** 2 / 2.0)
        Phi_ = regP(r + 0.5, xa_hi ** 2 / 2.0)
        lo[r] = top + Plo
        hi[r] = top + Phi_
    return lo, hi


# ----------------------------------------------------------------------
# validation at q = 2^24: full enumeration vs bracket
# ----------------------------------------------------------------------
def validate():
    q = 2.0 ** 24
    N = q - 2.0
    Nh = int(N // 2)                     # 8388607, N even so exact half
    rlist = [1, 5, 10, 17, 25, 34]
    acc = {r: [] for r in rlist}
    chunk = 2_000_000
    for start in range(1, Nh + 1, chunk):
        i = np.arange(start, min(start + chunk, Nh + 1), dtype=np.float64)
        v = (i - 0.5) / N
        x = norm.isf(v)
        lnx = np.log(x)
        for r in rlist:
            acc[r].append(logsumexp(2 * r * lnx))
    lo, hi = bulk_brackets(q, max(rlist))
    TOL = 1e-11   # double-precision allowance on the exact top-atom sums
    print("== VALIDATION q=2^24: exact full-enumeration bulk vs certified bracket ==")
    print(f"(containment up to rel tol {TOL:.0e} for float top-sums)")
    print(f"{'r':>4} {'beta_exact':>14} {'bracket_lo':>14} {'bracket_hi':>14} {'inside':>7} {'rel_width':>10}")
    ok = True
    for r in rlist:
        lS = logsumexp(np.array(acc[r]))
        beta = float(np.exp(lS + np.log(2.0) - np.log(N) - logdf(r)))
        inside = lo[r] * (1 - TOL) <= beta <= hi[r] * (1 + TOL)
        ok = ok and inside
        relw = (hi[r] - lo[r]) / beta
        print(f"{r:>4} {beta:>14.8e} {lo[r]:>14.8e} {hi[r]:>14.8e} {str(inside):>7} {relw:>10.2e}")
    print(f"validation {'PASS' if ok else 'FAIL'}\n")
    return ok


# ----------------------------------------------------------------------
# main scan machinery
# ----------------------------------------------------------------------
class Model:
    """lone-spike countermodel at scale q = n^4 (unit-variance reduced)."""

    def __init__(self, n_exp, T=200000):
        self.n_exp = n_exp
        self.n = 2.0 ** n_exp
        self.q = self.n ** 4
        self.lnq = 4 * n_exp * LN2
        self.L = int(np.ceil(self.lnq))          # CMK window: r <= L
        self.rmax = 2 * self.L                   # extended window
        self.blo, self.bhi = bulk_brackets(self.q, self.rmax, T)
        self.b1 = 0.5 * (self.blo[1] + self.bhi[1])   # unit bulk 2nd moment
        self.b1w = self.bhi[1] - self.blo[1]

    def ratios(self, t, r):
        """(lo, hi) bracket of m_{2r}/((2r-1)!! n^r) for spike height
        t*sqrt(n ln q), with Parseval-exact sigma rescale."""
        q, n, lnq = self.q, self.n, self.lnq
        m2 = t * t * lnq                          # M^2 / n
        scale = (q - n - m2) / ((q - 2.0) * self.b1)   # sigma^2 / n
        pref = (q - 2.0) / (q - 1.0)
        lspike = r * np.log(m2) - np.log(q - 1.0) - logdf(r)
        s = float(np.exp(lspike))
        f = pref * scale ** r
        return f * self.blo[r] + s, f * self.bhi[r] + s

    def Kreq(self, t, window, two_sided=True):
        """min slack K such that all moment ratios r<=window lie in
        [K^-r, K^r] (conservative bracket ends). Returns (K, binding r)."""
        best, rb = 1.0, 0
        for r in range(1, window + 1):
            rl, rh = self.ratios(t, r)
            k = rh ** (1.0 / r) if rh > 1.0 else 1.0
            if two_sided and rl < 1.0:
                k = max(k, (1.0 / rl) ** (1.0 / r))
            if k > best:
                best, rb = k, r
        return best, rb

    def t_spike(self, K, window, two_sided=True):
        """max t with Kreq(t) <= K (bisection); None if infeasible at t->0."""
        k0, _ = self.Kreq(0.05, window, two_sided)
        if k0 > K:
            return None
        a, b = 0.05, 6.0
        for _ in range(80):
            m = 0.5 * (a + b)
            if self.Kreq(m, window, two_sided)[0] <= K:
                a = m
            else:
                b = m
        return a

    def t_raw(self, K, window):
        """raw moment bound at the same data: min over r<=window."""
        best, rb = np.inf, 0
        for r in range(1, window + 1):
            val = float(np.exp((np.log(self.q - 1.0) + logdf(r)) / r)) * K / self.lnq
            if val < best:
                best, rb = val, r
        return np.sqrt(best), rb


# ----------------------------------------------------------------------
# Hermite-kernel Christoffel threshold (the essay's substituted bound)
# ----------------------------------------------------------------------
def log_hermite_kernel(x, j):
    """log K_j^Herm(x,x) = log sum_{k<=j} hhat_k(x)^2, orthonormal
    probabilists' Hermite wrt N(0,1). mpmath, overflow-safe."""
    x = mp.mpf(x)
    h0, h1 = mp.mpf(1), x
    s = h0 * h0 + h1 * h1
    for k in range(1, j):
        h2 = (x * h1 - mp.sqrt(k) * h0) / mp.sqrt(k + 1)
        s += h2 * h2
        h0, h1 = h1, h2
    return float(mp.log(s))


def hermite_threshold(lnq):
    """min t with K^Herm_j(t sqrt(ln q)) > q-1, j = ceil(ln q)."""
    j = int(np.ceil(lnq))
    lq = lnq  # log(q-1) ~ ln q

    def f(t):
        return log_hermite_kernel(t * np.sqrt(lnq), j) - lq

    a, b = 1.0, 3.5
    if f(a) > 0:
        return a
    for _ in range(60):
        m = 0.5 * (a + b)
        if f(m) <= 0:
            a = m
        else:
            b = m
    return 0.5 * (a + b)


# ----------------------------------------------------------------------
# true-kernel self-consistency demo (small scale, mpmath)
# ----------------------------------------------------------------------
def christoffel_demo(Nb=10000, tlist=(1.5, 1.8)):
    qm1 = Nb + 1                     # q-1 atoms total (spike + Nb bulk)
    q = qm1 + 1
    lnq = float(np.log(q))
    j = int(np.ceil(lnq))
    print(f"== CHRISTOFFEL SELF-CONSISTENCY DEMO: q-1={qm1} atoms, j=ceil(ln q)={j} ==")
    i = np.arange(1, Nb + 1, dtype=np.float64)
    xs = norm.isf((i - 0.5) / Nb)    # full unit-variance quantile bulk
    xmax = xs[0]
    xv = [mp.mpf(float(z)) for z in xs]
    # bulk power sums S_k = sum_i x_i^k, k = 0..2j (t-independent)
    S = [mp.mpf(Nb)]
    cur = [mp.mpf(1)] * Nb
    for k in range(1, 2 * j + 1):
        cur = [c * z for c, z in zip(cur, xv)]
        S.append(mp.fsum(cur))
    for t in tlist:
        M = mp.mpf(t) * mp.sqrt(lnq)
        mom = [(S[k] + M ** k) / qm1 for k in range(2 * j + 1)]
        H = mp.matrix(j + 1, j + 1)
        for a in range(j + 1):
            for b in range(j + 1):
                H[a, b] = mom[a + b]
        v = mp.matrix([M ** k for k in range(j + 1)])
        y = mp.lu_solve(H, v)
        Ktrue = float(sum(v[k] * y[k] for k in range(j + 1)))
        KH = float(mp.e ** mp.mpf(log_hermite_kernel(float(M), j)))
        print(f"  t={t:.2f}  M={float(M):.3f}  (bulk edge atom at {xmax:.3f}, "
              f"gap M-edge={float(M)-xmax:+.3f}, near neighbors in [M-1,M]: "
              f"{int(np.sum((xs >= float(M)-1) & (xs <= float(M))))})")
        print(f"    true kernel  K_j(M,M) = {Ktrue:.6g}   K/(q-1) = {Ktrue/qm1:.4f}"
              f"   (Christoffel bound mass<=1/K: {'SATISFIED' if Ktrue <= qm1*(1+1e-9) else 'VIOLATED'})")
        print(f"    Hermite proxy K^H_j(M,M) = {KH:.6g}   K^H/(q-1) = {KH/qm1:.4g}"
              f"   -> proxy {'WOULD FORBID the atom' if KH > qm1 else 'does not forbid'}")
        # moment ratios of the demo countermodel
        rats = [float(mom[2 * r]) / float(np.exp(logdf(r))) for r in range(1, j + 1)]
        kreq = max(max(rr, 1.0 / rr) ** (1.0 / (ridx + 1)) for ridx, rr in enumerate(rats))
        print(f"    demo moment ratios r=1..{j}: " +
              " ".join(f"{rr:.3f}" for rr in rats) + f"   (two-sided K_req = {kreq:.4f})")
    print()


# ----------------------------------------------------------------------
def main():
    print("PROBE 466 CMK LONE-SPIKE  (LANE R1)")
    print("conventions: log = ln;  M = t*sqrt(n ln q);  q = n^4;  CMK window r <= L = ceil(ln q)")
    print("Wick_r = (2r-1)!! n^r;  Parseval second moment = n(q-n)/(q-1) held EXACTLY.\n")

    validate()

    Ks = [1.05, 1.10, 1.20, 1.50, 2.00, float(np.e), 4.00]
    tgrid = [1.00, 1.20, np.sqrt(2.0), 1.60, 1.80, 2.00, np.sqrt(2 * np.e), 2.60, 3.00]

    for n_exp in [10, 14, 20, 30]:
        md = Model(n_exp)
        L, lnq, q = md.L, md.lnq, md.q
        print(f"===== n = 2^{n_exp}, q = n^4 = 2^{4*n_exp}, ln q = {lnq:.3f}, L = {L} =====")
        xmax = norm.isf(0.5 / (q - 2.0))
        print(f"bulk edge: x_max = Phi^-1(1-1/(2(q-2))) = {xmax:.4f} = "
              f"{xmax/np.sqrt(lnq):.4f}*sqrt(ln q)  (bulk itself reaches t ~ sqrt(2))")
        print("bulk Wick-ratio brackets beta_r (tail-truncation undershoot; midpoint-rule bracket):")
        for r in sorted({1, L // 2, L, 2 * L}):
            print(f"   r={r:>4}: beta in [{md.blo[r]:.6e}, {md.bhi[r]:.6e}]"
                  f"   K-cost (1/beta)^(1/r) = {(1.0/md.blo[r])**(1.0/r):.4f}")
        kfL = md.Kreq(0.05, L)[0]
        kf2L = md.Kreq(0.05, 2 * L)[0]
        print(f"bulk-only two-sided K floor: window L: {kfL:.4f}   window 2L: {kf2L:.4f}")
        print(f"(quantified: 'quantile bulk = Wick to depth 2j within K^r' holds two-sidedly"
              f" with K -> 1 at the CMK window)")

        print(f"\nK_req(t) two-sided, CMK window r<=L (binding r in parens); t^2/2 for reference:")
        for t in tgrid:
            k, rb = md.Kreq(t, L)
            k1, rb1 = md.Kreq(t, L, two_sided=False)
            print(f"   t={t:.4f}: K_req={k:.4f} (r*={rb})   one-sided={k1:.4f} (r*={rb1})"
                  f"   t^2/2={t*t/2:.4f}")

        print(f"\nK -> max spike height vs raw moment bound (SAME window r<=L, SAME K):")
        print(f"{'K':>6} {'t_spike(2-sided)':>17} {'t_spike(1-sided)':>17} {'t_spike(win 2L)':>16}"
              f" {'t_raw':>8} {'ratio':>7} {'t_sp^2/(2K)':>12} {'sqrt(2K)':>9} {'sqrt(2eK)':>10}")
        for K in Ks:
            ts2 = md.t_spike(K, L)
            ts1 = md.t_spike(K, L, two_sided=False)
            ts2L = md.t_spike(K, 2 * L)
            tr, rb = md.t_raw(K, L)
            s2 = f"{ts2:.4f}" if ts2 else "infeas"
            s1 = f"{ts1:.4f}" if ts1 else "infeas"
            s2L = f"{ts2L:.4f}" if ts2L else "infeas"
            rat = f"{ts2/tr:.4f}" if ts2 else "  --  "
            eff = f"{ts2*ts2/(2*K):.4f}" if ts2 else "  --  "
            print(f"{K:>6.3f} {s2:>17} {s1:>17} {s2L:>16} {tr:>8.4f} {rat:>7}"
                  f" {eff:>12} {np.sqrt(2*K):>9.4f} {np.sqrt(2*np.e*K):>10.4f}")

        tH = hermite_threshold(lnq)
        print(f"\nHermite-kernel Christoffel threshold t*_H(q) = {tH:.4f}"
              f"  (vs raw-bound sqrt(2)={np.sqrt(2):.4f}; essay claimed ~1)")
        print()

    christoffel_demo()

    print("=" * 76)
    print("VERDICT SUMMARY")
    print("=" * 76)
    print("""
1. LONE SPIKE WORKS.  For every slack K (down to the bulk floor K_bulk(q)->1),
   the countermodel achieves t_spike(K) = t_raw(K)*(1-o(1)) at the CMK-stated
   depth, two-sidedly, with Parseval EXACT and all masses exactly 1/(q-1).
   The abstract moment problem's answer IS the raw moment bound:
   C(K) = 2K(1+o(1)).  Positivity + equal masses + full moment sequence add
   NOTHING.  CMK-as-improvement is REFUTED; CMK-as-stated is trivially TRUE
   with C(K)=2K, i.e. it collapses to form (A) verbatim.
2. Extending the window to 2L (or any depth) does not help: the binding
   constraint sits at r ~ ln q, interior; deeper Wick data is slack.
3. SIGN settled: no factor improvement exists.  The essay's own
   Christoffel-with-Hermite mechanism, computed exactly (kernel threshold
   t*_H(q) = 1.385..1.400 rising to sqrt(2) from below; in the bulk region
   K^H_j(x,x) ~ e^{x^2/2} sqrt(2j-x^2)), REPRODUCES the moment-bound constant
   sqrt(2) -- it never improves it.  The essay's claimed "~1" rests on the
   substitution He_j(M) ~ M^j, invalid at M ~ sqrt(2j) (needs M >> j).
4. Edge crowding never fires: the lone spike has O(1) bulk atoms within unit
   distance (0 at t=1.8) versus the Omega(K_j/j) ~ q/log q neighbors the
   crowding mechanism would demand, yet the TRUE Christoffel bound is
   satisfied automatically (the spike deforms its own orthogonal polynomials
   -- one atom absorbs one quadrature node); only the illegitimate Hermite
   PROXY kernel would forbid it (K^H/(q-1) = 5.8 at t=1.5, 505 at t=1.8,
   while true K/(q-1) = 0.9967 / 1.0000).
5. Bulk quantization error quantified: beta_r = P(r+1/2, x_max^2/2) up to a
   certified midpoint bracket; undershoot is ~2x at r=L (K-cost 2^(1/L)->1)
   and ~q^-c at r=2L (K-cost ~1.1-1.3): no false-refutation leak.
CONSEQUENCE for the essay: Conjecture CMK dies as an improvement lever, and
the CMK-compose-TPS composition (sec 3 closing) dies with it -- a K^r-slack
Wick input can NEVER be sharpened past sqrt(2K) by abstract moment-problem
rigidity, because the lone spike realizes the full slack.  What survives:
form (A) itself, and the arithmetic question (prove K^r-Wick at depth ln q),
untouched.
""")


if __name__ == "__main__":
    main()
