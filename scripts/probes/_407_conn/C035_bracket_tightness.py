"""
C035 follow-up: is the two-sided bracket actually TIGHT, and what is the LOWER bracket's
ceiling? The headline claim is the two sides MEET at r ~ log m at scale Theta(sqrt(n log m)).

Key analytic facts to test:
  1. The LOWER bracket  L_r := (q E_r - n^{2r})/(q E_{r-1} - n^{2(r-1)}).
     As q -> infinity (prize: q >> n^{2r}), L_r -> E_r/E_{r-1}.  So L_r is just the
     consecutive ENERGY ratio (the n^{2r} corrections are negligible at prize scale).
     Therefore the LOWER bracket can NEVER exceed sup_r E_r/E_{r-1}, and at the relevant
     r it equals E_r/E_{r-1} ~ (2r-1)n -- which GROWS with r, not bounded by C*n.
  2. So the lower bracket's BEST bound on B^2 is sup_r (E_r/E_{r-1}). For the Gaussian model
     E_r=(2r-1)!! n^r this sup is unbounded (=(2r-1)n -> infty), but the moment method is
     only valid up to r_max ~ 2 log_n q (char-p depth wall). So the lower bracket caps at
     r_max, giving B^2 >= (2 r_max - 1) n ~ (4 log_n q) n -- and the upper at the SAME r is
     (q E_r)^{1/r}, which at r ~ log q gives ~ 2 n log q.  The two do NOT meet at the same r.

Demonstrate: take the char-0 Gaussian energy E_r=(2r-1)!! n^r (the model C035 invokes) and
compute BOTH brackets as functions of r at prize-scale q. Find the r that maximizes LOWER and
the r that minimizes UPPER, and show they are DIFFERENT and the gap between best-lower and
best-upper is large (the bracket is NOT tight; it does not pin B at a single law).
"""
import math
from math import lgamma, log, exp

def log_doublefact_odd(k):
    """log((2k-1)!!) = log( (2k)! / (2^k k!) )."""
    # (2k-1)!! = (2k)!/(2^k k!)
    return lgamma(2*k+1) - k*log(2) - lgamma(k+1)

def analyze(n, beta):
    q = n ** beta
    logq = beta * log(n)
    m = q / n
    logm = log(m)
    # r_max for char-p validity (norm bound): q > (2r)^{n/2}  => r < q^{2/n}/2.
    # at prize n>=2^20 this is huge, but the moment-method DEPTH wall (CharSumMomentDeepWall)
    # is r_max ~ 2 log_n q.  Use r_max = 2 logq/log n = 2 beta.
    rmax_depth = max(2, int(2*beta))
    # char-0 model E_r = (2r-1)!! n^r  (the model C035 invokes for "TRUE max of m sub-Gaussians")
    def logE(r):
        if r == 0: return 0.0
        return log_doublefact_odd(r) + r*log(n)
    print(f"n={n} q=n^{beta}={q:.3e}  logq={logq:.2f}  m=q/n  logm={logm:.2f}  "
          f"depth r_max~2beta={rmax_depth}")
    print(f"  {'r':>3} {'E_r/E_(r-1)':>12} {'=(2r-1)n?':>10} {'LOWER(B^2)':>11} "
          f"{'UPPER(B^2)':>11} {'sqrt(LOW)':>9} {'sqrt(UP)':>9}")
    best_lower = (0, -1e9)
    best_upper = (0, 1e30)
    for r in range(1, 40):
        # LOWER = (q E_r - n^{2r})/(q E_{r-1} - n^{2(r-1)})
        # work in logs but keep the n^{2r} correction; at prize q E_r >> n^{2r} for r small
        lEr = logq + logE(r)
        lErm = logq + logE(r-1)
        # n^{2r} vs q E_r:  log(n^{2r}) = 2r log n ; subtract corrections in linear space if comparable
        corr_r = 2*r*log(n)
        corr_rm = 2*(r-1)*log(n)
        # q E_r - n^{2r} = exp(lEr) (1 - exp(corr_r - lEr))
        try:
            num = exp(lEr) * (1 - exp(corr_r - lEr))
            den = exp(lErm) * (1 - exp(corr_rm - lErm))
            lower = num/den if den > 0 else float('nan')
        except OverflowError:
            lower = exp(lEr - lErm)  # ratio E_r/E_{r-1}
        upper = exp((logq + logE(r))/r)   # (q E_r)^{1/r}
        ratio_over_n = exp(logE(r)-logE(r-1))/n
        marker = "" if r <= rmax_depth else "  (>r_max)"
        if r <= 12 or r == rmax_depth:
            print(f"  {r:>3} {exp(logE(r)-logE(r-1)):12.2f} {(2*r-1)*n:10.0f} "
                  f"{lower:11.2f} {upper:11.2f} {math.sqrt(max(lower,0)):9.2f} "
                  f"{math.sqrt(upper):9.2f}{marker}")
        if r <= rmax_depth and lower > best_lower[1]:
            best_lower = (r, lower)
        if r <= rmax_depth and upper < best_upper[1]:
            best_upper = (r, upper)
    print(f"  >>> best LOWER bound on B^2 = {best_lower[1]:.1f} (sqrt={math.sqrt(best_lower[1]):.2f}) "
          f"at r={best_lower[0]}")
    print(f"  >>> best UPPER bound on B^2 = {best_upper[1]:.1f} (sqrt={math.sqrt(best_upper[1]):.2f}) "
          f"at r={best_upper[0]}")
    gap = best_upper[1]/best_lower[1] if best_lower[1] > 0 else float('inf')
    print(f"  >>> BRACKET GAP (upper/lower, B^2 scale) = {gap:.2f}x ; "
          f"meet at same r? {'YES' if best_lower[0]==best_upper[0] else 'NO'}")
    print(f"  >>> prize target sqrt(2 n logq) = {math.sqrt(2*n*logq):.2f} ; "
          f"sqrt(n) = {math.sqrt(n):.2f}")
    print()

# prize-shaped: thin dyadic subgroup, q = n^beta, beta 4-5
for n, beta in [(2**10, 4.5), (2**20, 4.5), (2**30, 4.5), (2**30, 5.0)]:
    analyze(n, beta)
