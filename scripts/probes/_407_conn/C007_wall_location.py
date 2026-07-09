"""
C007 part 2 (log-space): is the binomial crossover r* the PRIZE WALL location?

Use lgamma for log2-binomials so prize n=2^30 is instant. We do NOT need exact
integers to compare lg(budget/p) against -128 or to locate the crossover sign flip.

m = 1.  budget(r) = C(n,r)/r ;  supply(r) = 2^r C(N,r) ,  N=n/2.
PIN holds while budget < supply (the pin lower-half non-vacuity).
Prize: pin must hold at eps* = 2^-128, p ~ n^beta = 2^{beta*mu}.
"""
from math import lgamma, log2, log

L2 = log(2.0)

def lg_choose(n, k):
    if k < 0 or k > n:
        return float('-inf')
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / L2

def lg_budget(n, r):
    return lg_choose(n, r) - log2(r)            # C(n,r)/r

def lg_supply(n, r):
    return r + lg_choose(n // 2, r)             # 2^r C(N,r)

def crossover(n):
    """smallest r where budget >= supply (sign flip of lg_supply - lg_budget)."""
    lo, hi = 2, n // 2
    def pin(r):
        return lg_budget(n, r) < lg_supply(n, r)
    if pin(hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if pin(mid):
            lo = mid + 1
        else:
            hi = mid
    return lo

def analyze(mu, beta):
    n = 2 ** mu
    lgp = beta * mu
    rstar = crossover(n)
    import math
    sq = int(math.isqrt(n))
    print(f"\n--- n=2^{mu}={n}, p~2^{lgp} (beta={beta}), target eps*=2^-128, r*={rstar} ---")
    print(f"{'r':>10} {'lg budget':>11} {'lg supply':>11} {'lg(bud/p)':>11} {'PIN?':>5} "
          f"{'bud/p<=2^-128?':>15}   note")
    pts = sorted(set([2, 3, sq, rstar, rstar - 1, rstar // 2, max(2, rstar // 10),
                      max(2, rstar // 100)]))
    pts = [r for r in pts if 2 <= r <= n // 2]
    for r in pts:
        lb, ls = lg_budget(n, r), lg_supply(n, r)
        pin = lb < ls
        note = ""
        if r == rstar:
            note = "<== r* crossover (PIN->WALL)"
        elif r == sq:
            note = "<== sqrt(n): Lean choose_bulk proven edge"
        print(f"{r:>10} {lb:>11.2f} {ls:>11.2f} {lb-lgp:>11.2f} {str(pin):>5} "
              f"{str(lb-lgp<=-128):>15}   {note}")
    # find largest r with budget/p <= 2^-128  (the actual eps*-feasible band)
    # budget/p decreasing then increasing in r; we want the r-RANGE where bud/p<=-128.
    feas = [r for r in range(2, min(n//2, 4000)) if lg_budget(n, r) - lgp <= -128]
    if feas:
        print(f"    eps*-feasible band (bud/p<=2^-128) within r<4000: r in [{feas[0]},{feas[-1]}]")
    else:
        print(f"    NO r in [2,4000) gives bud/p<=2^-128  (so pin never reaches prize eps*)")
    return rstar

for beta in (4, 5):
    for mu in (10, 20, 30):
        analyze(mu, beta)
