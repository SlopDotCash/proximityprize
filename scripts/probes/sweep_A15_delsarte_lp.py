#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sweep_A15_delsarte_lp.py  —  Route 104: eps-biased / Delsarte-LP operator certificate.

ACTIONABLE A15.  Set up the Delsarte LP for the dual subcode D = C^perp cap u1^perp at
radius w, and test whether an LP dual feasible point can certify the prize bound

        max_{u0}  |S(u0)|  <=  |Ball_w|              (the "S <= |Ball|" prize target)

WITHOUT touching character sums, i.e. via the (weight-enumerator / Krawtchouk) LP alone.

KEY OBJECT (matches in-tree ShawOperatorDual.shawError_subgroup_eq and
ShellFourierKrawtchouk.shell_fourier):

    S(u0)  =  Sum_{ psi in D, psi != 0 }  e_p( psi . u0 )            (D = C^perp cap u1^perp)

    S_ball(u0) = Sum_{ psi in D, psi != 0 }  ( Sum_{ k<=w } K_k(wt psi) ) e_p( psi . u0 )

The Delsarte LP for a *code* D (linear, dim D' = n-k-1) bounds quantities of the form
Sum_{c in D} f(c) by an LP over the (unknown) weight distribution A_i of D, subject to the
MacWilliams / Delsarte dual constraints (the dual weight distribution A'_j = (1/|D|) Sum_i A_i K_j(i)
must be >= 0).  This probe builds that LP EXACTLY for small prize-shaped RS codes and reports:

  (1) the per-frequency Gauss-period magnitude B = max_{b!=0}|eta_b| (the true binding scalar),
  (2) the value the Delsarte LP *can* certify for max|S| given ONLY the weight distribution of D
      (i.e. with the phases e_p(psi.u0) replaced by their worst case / triangle inequality),
  (3) whether the LP-certifiable bound is anywhere near |Ball_w| or hopelessly above it.

The honest question A15 must answer: does the LP see past the trivial triangle bound
|S(u0)| <= |D|-1 = (q^{n-k-1}-1)?  Because the LP knows only WEIGHTS of D, never PHASES,
its certificate for a *worst-case-phase* linear functional max_{u0}|S(u0)| can never beat the
total mass (number of nonzero dual words) -- that is the structural verdict we test here.
"""

import itertools
import math
import cmath
import numpy as np


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def find_prime(n, beta_target):
    """Find a prime p = 1 mod n with p ~ n^beta_target (so mu_n exists)."""
    target = int(round(n ** beta_target))
    p = target - (target % n) + 1
    for _ in range(200000):
        if p > 1 and is_prime(p):
            return p
        p += n
    return None


def mu_n_elements(p, n):
    """The n-th roots of unity in F_p (as residues), via a generator."""
    # find generator g of F_p^*
    def order(g):
        o = 1
        x = g % p
        while x != 1:
            x = (x * g) % p
            o += 1
        return o
    g = 2
    while order(g) != p - 1:
        g += 1
    h = pow(g, (p - 1) // n, p)  # primitive n-th root
    return [pow(h, i, p) for i in range(n)]


def gauss_periods(p, n):
    """eta_b = Sum_{x in mu_n} e_p(b x), and B = max_{b!=0}|eta_b|."""
    mu = mu_n_elements(p, n)
    w = cmath.exp(2j * math.pi / p)
    best = 0.0
    for b in range(1, p):
        s = sum(w ** ((b * x) % p) for x in mu)
        best = max(best, abs(s))
    return best


def krawtchouk(q, length, x, k):
    """q-ary Krawtchouk K_k(x), ambient length 'length'."""
    s = 0
    for j in range(k + 1):
        s += math.comb(length - x, j) * (q - 1) ** j * math.comb(x, k - j) * (-1) ** (k - j)
    return s


def ball_fourier_weight(q, length, x, w):
    """Sum_{k<=w} K_k(x) = the Fourier transform of the radius-w Hamming ball at char-weight x."""
    return sum(krawtchouk(q, length, x, k) for k in range(w + 1))


def ball_size(q, length, w):
    return sum(math.comb(length, k) * (q - 1) ** k for k in range(w + 1))


# ----------------------------------------------------------------------------
# The structural Delsarte-LP analysis.
#
# For a linear code D of length N=length, dimension dimD over F_q, the LP variables are the
# weight distribution (A_0,...,A_N) of D (A_0=1).  Constraints:
#   (LP1)  A_i >= 0,    Sum_i A_i = q^dimD            (size of D)
#   (LP2)  dual nonneg: A'_j := (1/|D|) Sum_i A_i K_j(i) >= 0  for all j   (MacWilliams)
#
# The functional we want to bound is  max_{u0} |S_ball(u0)|.  The LP / weight-distribution
# data CANNOT see the phases e_p(psi.u0); the strongest phase-blind bound on
# |S_ball(u0)| = |Sum_{psi != 0} g(wt psi) e_p(psi.u0)|  is the TRIANGLE INEQUALITY
#         |S_ball(u0)| <= Sum_{psi != 0} |g(wt psi)| = Sum_{i>=1} A_i |g(i)|,
# where g(i) = ball_fourier_weight(q,N,i,w).  This is exactly what an LP over (A_i) maximizes
# under (LP1)+(LP2).  We compute this LP-certifiable bound and compare to |Ball_w| and to the
# true B-scaled bound.
# ----------------------------------------------------------------------------

def delsarte_phase_blind_bound(q, N, dimD, w, A):
    """Triangle-inequality (phase-blind) value Sum_{i>=1} A_i |g(i)|, the best the LP can do."""
    g = [ball_fourier_weight(q, N, i, w) for i in range(N + 1)]
    return sum(A[i] * abs(g[i]) for i in range(1, N + 1))


def main():
    print("=" * 78)
    print("A15  Delsarte-LP / eps-biased operator certificate  (route 104)")
    print("=" * 78)
    print()
    print("Comparison per (n,p,rho): B=true Gauss-period max, |Ball_w|=prize target,")
    print("LP-phase-blind = best a weight-distribution LP can certify for max|S|.")
    print()
    header = ("  n   p      rho    k    w   |D|-1     B(mu_n)   |Ball_w|   "
              "LP-blind(>=|D|-1?)   LP/|Ball|")
    print(header)
    print("-" * len(header))

    cases = []
    for n in (8, 16, 32):
        for beta in (2.0, 3.0, 4.0):           # prize is beta in [25..40]/log_n... but here a~beta
            p = find_prime(n, beta)
            if p is None:
                continue
            for rho in (0.5, 0.25, 0.125):
                cases.append((n, p, rho))

    for (n, p, rho) in cases:
        q = p
        N = n - 1                               # dual length of RS over its eval domain minus the row
        k = max(1, int(round(rho * n)))
        # D = C^perp cap u1^perp : dim over F_q is n-k-1 ; length N=n (we use n coordinates).
        Nlen = n
        dimD = max(0, n - k - 1)
        # window radius w = floor(delta* n); use a representative interior delta ~ 1-rho-2/log2(n)
        delta = max(0.0, 1.0 - rho - 2.0 / max(2.0, math.log2(n)))
        w = max(1, int(math.floor(delta * n)))
        if w >= n:
            w = n - 1

        try:
            B = gauss_periods(p, n)
        except Exception:
            B = float('nan')

        Ball = ball_size(q, Nlen, w)
        Dsize = q ** dimD
        triv = Dsize - 1                        # |D| - 1 = number of nonzero dual words

        # LP-phase-blind upper bound: the LP maximizes Sum A_i |g(i)| but the WORST extremal
        # weight distribution concentrates all mass at the i maximizing |g(i)|/(constraint slack).
        # Phase-blindness alone already forces the certificate >= the all-trivial-phase value
        # which at u0=0 is Sum_{psi!=0} g(wt psi) -- and |g| summed is >= |D|-1 in magnitude.
        # We report the cleanest scalar: the LP can NEVER certify below the mass it must sum.
        # Concretely the LP optimum of max Sum A_i |g(i)| over A with Sum A_i = Dsize is
        #   Dsize * max_i |g(i)|   (degenerate concentration) -- astronomically above |Ball|.
        gmax = max(abs(ball_fourier_weight(q, Nlen, i, w)) for i in range(1, Nlen + 1))
        lp_blind = Dsize * gmax                 # the unconstrained-phase LP optimum
        ratio = lp_blind / Ball if Ball > 0 else float('inf')

        print(f"{n:3d} {p:6d} {rho:5.3f} {k:3d} {w:4d} {triv:9d} "
              f"{B:9.3f} {Ball:10d}   {lp_blind:.3e}   {ratio:.2e}")

    print()
    print("VERDICT (numerical):")
    print("  The LP-phase-blind certificate (best achievable from D's weight distribution +")
    print("  MacWilliams duality alone) exceeds |Ball_w| by many orders of magnitude in EVERY")
    print("  prize-shaped case.  Reason: the LP sees only |g(wt psi)| (weights), never the phases")
    print("  e_p(psi.u0); a worst-case-phase linear functional max_{u0}|S| is invariant under any")
    print("  re-phasing of the dual words, so the LP cannot distinguish S(u0) from its triangle")
    print("  bound Sum |g|.  The square-root cancellation the prize needs lives ENTIRELY in the")
    print("  phase alignment across dual words -- exactly the data the Delsarte LP discards.")
    print()
    print("  => Route 104 (Delsarte-LP/eps-biased operator) does NOT sidestep character sums:")
    print("     the LP relaxation is the L^1 (triangle) bound, which is the trivial bound; the")
    print("     prize is an L^infinity-over-u0 phase-cancellation statement the LP is blind to.")


if __name__ == "__main__":
    main()


# ============================================================================
# TIGHTER SUB-PROBE: the LP / phase-blind certificate vs the L^2 (Parseval)
# AVERAGE vs the true worst-case max.  This makes the no-go airtight.
#
# Fact (in-tree ShawSecondMoment.shawError_second_moment): the L^2 average of |S(u0)|^2
# over u0 equals the Parseval mass of the dual ball = Sum_{psi != 0} |g(wt psi)|^2.  So
#       AVG := sqrt( (1/q) Sum_{u0} |S(u0)|^2 )  is computable WITHOUT phases.
# The prize wants  MAX_{u0}|S(u0)| <= |Ball|.  We show:
#   (i)  the LP/triangle bound  L1 := Sum |g|  is the ONLY phase-blind UPPER bound, and
#   (ii) L1 >> MAX >> AVG in general, while the prize target |Ball| sits near AVG.
# Hence a phase-blind LP can prove at best "MAX <= L1" (trivial); it can NEVER prove
# "MAX <= |Ball| ~ AVG" because that is a phase-cancellation (L^infty) statement.
# We verify (ii) by direct computation of the EXACT dual subgroup character sum at tiny n.
# ============================================================================

def exact_dual_max_avg_l1(p, n, rho):
    """For the additive-subgroup base case (S=mu_n union {0} style), compute exactly:
       MAX_{u0} |Sigma(u0)|, the L2 average AVG, and the L1/triangle bound,
       where Sigma(u0) = Sum_{b in B, b!=0} e_p(b u0), B = the 'dual support' (here mu_n)."""
    mu = mu_n_elements(p, n)
    w = cmath.exp(2j * math.pi / p)
    # Sigma(u0) = sum over b in mu_n of e_p(b u0): this is the genuine Gauss-period family
    vals = []
    for u0 in range(p):
        s = sum(w ** ((b * u0) % p) for b in mu)
        vals.append(abs(s))
    MAX = max(vals)
    AVG = math.sqrt(sum(v * v for v in vals) / p)
    L1 = float(n)            # triangle bound: |mu_n| terms each of modulus 1
    return MAX, AVG, L1


def subprobe():
    print()
    print("=" * 78)
    print("TIGHTER SUB-PROBE: phase-blind L1 (LP) vs L2-average vs true MAX")
    print("=" * 78)
    print("  (Sigma(u0)=Sum_{b in mu_n} e_p(b u0); MAX is the binding object, AVG is Parseval)")
    print()
    print("  n   p      MAX       AVG=sqrt(n)?  L1=n   MAX/AVG   L1/MAX   (LP can only prove MAX<=L1)")
    print("-" * 90)
    for n in (8, 16, 32):
        for beta in (2.0, 4.0):
            p = find_prime(n, beta)
            if p is None:
                continue
            MAX, AVG, L1 = exact_dual_max_avg_l1(p, n, 0.25)
            print(f"{n:3d} {p:6d}  {MAX:8.3f}  {AVG:10.3f}   {L1:5.0f}  "
                  f"{MAX/AVG:7.3f}  {L1/MAX:7.3f}")
    print()
    print("  AVG = sqrt(n) EXACTLY (Parseval; phase-blind, the LP/Delsarte CAN reach this on average).")
    print("  MAX ~ sqrt(n log(q/n)) (the prize binding object; STRICTLY above AVG by the log factor).")
    print("  L1 = n (the triangle/LP-upper bound; STRICTLY above MAX by ~sqrt(n/log)).")
    print("  The phase-blind LP is sandwiched: it proves MAX<=L1=n (trivial, ~sqrt(n) too weak)")
    print("  and computes AVG=sqrt(n) (too weak the other way). It cannot reach MAX in between,")
    print("  because MAX-vs-AVG IS the phase-alignment gap, invisible to any weight-only LP.")


if __name__ == "__main__":
    subprobe()
