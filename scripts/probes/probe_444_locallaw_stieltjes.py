#!/usr/bin/env python3
r"""
probe_444_locallaw_stieltjes.py -- UNTRIED LEAD assessment: local-law / Stieltjes self-consistent
equation for the DETERMINISTIC point process of Gauss-period values |eta_b| over the m cosets.

LEAD (from #444 comments, flagged untried):
  Randomize the CHARACTER b (parameter family), not the graph. Apply EKYY local-law /
  resolvent self-consistent-equation to the deterministic kernel
        K(b,c) = (1/n) sum_{x in mu_n} e_p((b-c) x)        (Fejer/Dirichlet kernel on mu_n)
  to get an edge bound lambda_2 = M(n) directly.

ASSESS: does the self-consistent equation CLOSE deterministically for this kernel, or does it
need the random/universality input the meta-theorem forbids?

PRIZE REGIME ONLY: mu_n = PROPER order-n subgroup of F_p^*, n=2^mu, n | p-1, p = 1 mod n,
n << sqrt(p), beta = log_n p in [4,5], m = (p-1)/n. NEVER the full group.

What M(n) actually is (CLAUDE.md): M(n) = max_{b != 0 mod p} | sum_{x in mu_n} e_p(b x) |
                                        = max_b | n * eta_b |   (eta = period normalized by 1/n? -- careful)
We use the UNNORMALIZED Gauss period  S_b = sum_{x in mu_n} e_p(b x),  M = max_{b!=0} |S_b|.
Orbit-invariance: S_{zeta b} = S_b for zeta in mu_n, so there are only m = (p-1)/n distinct
values indexed by cosets b mu_n in F_p^* / mu_n  (plus the value at b=0 which is n, excluded).

THE KERNEL.  Index the m cosets by representatives b_1..b_m. Define the m x m Hermitian matrix
        K[i,j] = (1/n) sum_{x in mu_n} e_p((b_i - b_j) x).
Diagonal K[i,i] = 1. This is a Gram matrix:  K[i,j] = <v_i, v_j>/n where v_i = (e_p(b_i x))_{x in mu_n}
in C^n.  So K = (1/n) V V^*  with V the m x n matrix V[i,x] = e_p(b_i x).  K is PSD, rank <= n.

CLAIM TO TEST (does the lead's object even carry M?):
  The Gauss period S_b is a LINEAR functional of the row, not an eigenvalue of K.
  We must check: is M(n) recoverable as a SPECTRAL EDGE of K (or of a related operator),
  so that a local law on K's spectrum bounds M? Or is M orthogonal to K's spectrum?

TESTS:
 (T1) Build K exactly (mod-p integer phases, proper subgroup). Verify K = (1/n) V V^*, rank,
      and that its eigenvalues are {(#cosets in each fiber)...} -- i.e. K's spectrum is the
      DESIGN spectrum (multiplicities), NOT the period values. Edge of K.
 (T2) The TRUE object: S_b = sum_x e_p(b x). Relate to K. Show S_b = n * K[i, 0-row]? The
      all-ones / b=0 reference. Test whether max|S_b| = spectral edge of ANY natural operator
      built from K deterministically.
 (T3) STIELTJES SELF-CONSISTENT EQUATION. The empirical spectral measure of the value
      process {Re(S_b)} (or {|S_b|}) over cosets: m_N(z) = (1/m) sum_b 1/(S_b - z).
      Local law asks: does m_N satisfy m = 1/(-z - sigma^2 m) + o(1) (semicircle SCE) with a
      DETERMINISTIC error? Test edge-rigidity: is the largest value |S_b| pinned at
      2 sigma sqrt() + rigidity-fluctuation, or does it float (= the BGK gap)?
 (T4) The DECISIVE test for "needs RMT input". The SCE closes deterministically iff the
      kernel's resolvent has a deterministic self-consistent profile -- equivalently iff the
      values S_b are a DETERMINISTIC function whose empirical measure + edge are pinned by
      finitely many moments with deterministic error. Compare:
        edge_predicted_by_SCE(low moments)  vs  true M(n)  vs  sqrt(n log m).
      If the SCE edge needs ALL moments (r ~ log m) to track M, the deterministic closure
      FAILS = same fate as C077 (free cumulants) and the moment wall = reduce-to-wall.
      If the SCE edge from O(1) moments tracks M with shrinking error as m grows, SURVIVES.
"""
import cmath, math
import numpy as np


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0: return False
        i += 2
    return True


def prize_prime(n, beta_lo, beta_hi):
    lo = int(n ** beta_lo); hi = int(n ** beta_hi)
    start = max(lo, n + 1)
    first = start + ((1 - start) % n)  # p = 1 mod n
    p = first
    while p < hi:
        if is_prime(p):
            # require PROPER subgroup with non-trivial odd cofactor so mu_n is genuinely thin
            if (p - 1) // n > 1:
                return p
        p += n
    return None


def primitive_root(p):
    if p == 2: return 1
    fac = []
    pp = p - 1; d = 2
    while d * d <= pp:
        if pp % d == 0:
            fac.append(d)
            while pp % d == 0: pp //= d
        d += 1
    if pp > 1: fac.append(pp)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    return None


def order_n_subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    H = []
    x = 1
    for _ in range(n):
        H.append(x); x = x * h % p
    assert len(set(H)) == n, "subgroup not order n"
    assert 0 not in H
    return H, g


def cosets(p, n, g):
    """Representatives of F_p^* / mu_n: g^0, g^1, ..., g^{m-1} (m = (p-1)/n)."""
    m = (p - 1) // n
    reps = [pow(g, j, p) for j in range(m)]
    return reps, m


def gauss_period(b, H, p):
    """S_b = sum_{x in H} e_p(b x) = sum exp(2 pi i b x / p)."""
    s = 0j
    w = 2 * math.pi / p
    for x in H:
        s += cmath.exp(1j * w * (b * x % p))
    return s


def main():
    print("=" * 100)
    print("probe_444_locallaw_stieltjes : does the resolvent SCE close DETERMINISTICALLY on K(b,c)?")
    print("=" * 100)
    cases = [(8, 4.0), (16, 4.0), (32, 4.0), (64, 4.0), (16, 5.0), (32, 5.0)]
    summary = []
    for n, beta in cases:
        p = prize_prime(n, beta, beta + 0.6)
        if p is None:
            print(f"n={n} beta={beta}: no prize prime"); continue
        H, g = order_n_subgroup(p, n)
        reps, m = cosets(p, n, g)
        # one representative per coset; S is coset-invariant so this is the full value set
        S = np.array([gauss_period(b, H, p) for b in reps], dtype=complex)
        absS = np.abs(S)
        M = absS.max()
        # sigma^2 = (1/m) sum |S_b|^2  (the L2 size). Parseval: sum_{b!=0} |S_b|^2 = n(p-1) - n^2
        # over ALL b!=0; per coset (each value repeated n times among the p-1 nonzero b):
        # sum_{cosets} |S|^2 * n = n(p-1)-n^2  => mean_coset |S|^2 = (p-1-n)/m * ... let's just measure.
        sigma2 = (absS ** 2).mean()
        logm = math.log(m)

        # ---- T1: the kernel K and its spectrum ----
        # K[i,j] = (1/n) sum_x e_p((b_i - b_j) x). Build V (m x n), K = (1/n) V V^*.
        w = 2 * math.pi / p
        # to keep it feasible, cap m for the kernel spectrum (full V V^* is m x m)
        mcap = min(m, 1200)
        repsK = reps[:mcap]
        V = np.empty((mcap, n), dtype=complex)
        for i, b in enumerate(repsK):
            for xi, x in enumerate(H):
                V[i, xi] = cmath.exp(1j * w * (b * x % p))
        K = (V @ V.conj().T) / n
        evK = np.linalg.eigvalsh(K)
        edgeK = evK.max().real
        # rank of K = n (generic) -> nonzero eigenvalues; edge of design spectrum

        # ---- T3/T4: Stieltjes / moment-reconstructed edge of the VALUE process Re(S) ----
        # Use Re(S_b) as the real spectrum (the lead targets |eta_b|; Re is the natural
        # real-symmetric value with mean ~0 and the same sqrt cancellation).
        X = S.real.copy()
        X -= X.mean()
        varX = (X ** 2).mean()
        # moments normalized so that an O(1) edge is sqrt(2 sigma^2 log m)-scale
        # SCE/semicircle edge prediction from only mu_2: 2*sqrt(varX) (semicircle radius)
        edge_sc = 2 * math.sqrt(varX)
        trueM_re = np.abs(X).max()
        # The "deterministic local-law edge" would be edge_sc + rigidity. Compare to true.
        # rigidity scale: a genuine deterministic local law pins max within O(m^{-2/3}) of edge_sc.

        # ---- the LEAD'S CRUX: does the edge need high moments? ----
        # reconstruct edge from truncated moment sequence via the (classical) Stieltjes
        # self-consistent / orthogonal-polynomial (Jacobi) recursion. We use the empirical
        # measure of X and its Chebyshev/Jacobi continued fraction; truncating at order 2r
        # uses only the first r moments. Edge_r = largest root of the order-r orthogonal poly
        # (Gauss quadrature node) -- the standard "moment -> support edge" estimator.
        def edge_from_moments(vals, r):
            # build the (r+1)-point Gauss quadrature from the empirical measure's first 2r+1
            # moments via the Lanczos/Stieltjes recurrence; the largest node approximates the
            # spectral edge using only low moments (deterministic, no randomness).
            v = vals.astype(float)
            # three-term recurrence (Stieltjes procedure) for the empirical measure
            # weights uniform 1/len
            wts = np.full(len(v), 1.0 / len(v))
            # Lanczos on the multiplication operator
            alpha = np.zeros(r + 1); beta = np.zeros(r + 1)
            q = np.ones(len(v)); q = q / math.sqrt((wts * q * q).sum())
            qprev = np.zeros(len(v))
            for k in range(r + 1):
                z = v * q
                a = (wts * q * z).sum(); alpha[k] = a
                z = z - a * q - (beta[k] if k > 0 else 0.0) * qprev
                # reorthogonalize
                z = z - (wts * q * z).sum() * q
                b2 = (wts * z * z).sum()
                if b2 <= 1e-18:
                    r = k; break
                bb = math.sqrt(b2)
                if k + 1 <= r:
                    beta[k + 1] = bb
                qprev = q; q = z / bb
            rr = r
            J = np.diag(alpha[:rr + 1]) + np.diag(beta[1:rr + 1], 1) + np.diag(beta[1:rr + 1], -1)
            nodes = np.linalg.eigvalsh(J)
            return nodes.max()

        edges = {}
        for r in [1, 2, 4, 8, min(16, m // 2)]:
            try:
                edges[r] = edge_from_moments(X, r)
            except Exception as e:
                edges[r] = float('nan')

        ratio = M / math.sqrt(n * logm) if logm > 0 else float('nan')
        print(f"\n--- n={n} beta={beta} p={p} m={m} ---")
        print(f"  M = max|S_b|           = {M:.4f}")
        print(f"  M / sqrt(n log m)      = {ratio:.4f}   (prize: BOUNDED <= C)")
        print(f"  M / sqrt(n)            = {M/math.sqrt(n):.4f}")
        print(f"  sigma^2 = mean|S|^2    = {sigma2:.4f}   (~ n? {sigma2/n:.4f}*n)")
        print(f"  K edge (design spec)   = {edgeK:.4f}   K rank-nonzero ev range "
              f"[{evK[evK>1e-9].min():.3f},{edgeK:.3f}]")
        print(f"  -- VALUE process Re(S) (centered), var = {varX:.4f} = {varX/n:.4f}*n")
        print(f"  semicircle edge 2sqrt(var) = {edge_sc:.4f}   true max|Re S| = {trueM_re:.4f}  "
              f"excess = {trueM_re/edge_sc:.4f}")
        print(f"  STIELTJES moment-edge (Gauss-quad node), should track true max if SCE closes low:")
        for r in sorted(edges):
            print(f"     r={r:>2} moments -> edge = {edges[r]:.4f}   "
                  f"(edge/true = {edges[r]/trueM_re:.4f})")
        summary.append((n, beta, m, ratio, trueM_re / edge_sc, edges, trueM_re))

    print("\n" + "=" * 100)
    print("VERDICT INPUTS")
    print("=" * 100)
    print(" (A) Does M live on K's spectrum?  K's edge is the DESIGN/multiplicity edge, "
          "independent of which\n     period is large -- it is b-INSENSITIVE. Check above: K edge "
          "vs M scaling.")
    print(" (B) Does the Stieltjes/SCE edge from O(1) moments track true M?  If edge_r SATURATES "
          "below true M\n     and the gap GROWS with m (needs r~log m), the deterministic closure "
          "FAILS = reduce-to-wall.")
    print(" (C) semicircle-excess true/edge_sc: if it grows like sqrt(log m), the edge is a "
          "TAIL/high-moment\n     effect a local law cannot pin without the random input "
          "(= need-RMT-input).")
    # excess scaling vs log m
    print("\n excess (true/edge_sc) vs log m:")
    for (n, beta, mm, ratio, exc, edges, tm) in summary:
        print(f"   n={n:>3} beta={beta} m={mm:>7}  log m={math.log(mm):.2f}  excess={exc:.4f}  "
              f"M/sqrt(n log m)={ratio:.4f}")


if __name__ == "__main__":
    main()
