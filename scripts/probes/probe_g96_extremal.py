#!/usr/bin/env python3
"""G96 probe A: the constrained extremal problem for the house of Gauss periods.

For real primes p, n | p-1, mu_n = n-th roots of unity in F_p^x:
  - compute the m = (p-1)/n distinct period values v_1..v_m exactly-enough (longdouble),
  - compute true power sums P_r = sum v^r (r <= Dmax),
  - estimate max-house(D) = sup { H : a unit atom at +-H plus a nonnegative measure of mass
    m-1 on [-n,n] has moments P_1..P_D } via Hankel PSD feasibility of the bulk,
  - compare vs true M, sqrt(n log(p/n)), and the moment ladder min_{2r<=D} P_{2r}^{1/2r}.

Scope (numerical diagnostic, not a certificate).  The set of feasible spike heights need
NOT be an interval: e.g. n=1, m=2, (P_0,P_1,P_2)=(2,0,2) (unit atoms at -1,+1) is feasible
only at H=1, since removing a unit atom at H in [0,1) leaves second moment 2-H^2 > 1 for the
remaining mass 1 on [-1,1].  A monotone bisection therefore can return values far below the
true sup (the former version returned 0 on that example and returned maxima below the true
period house M on (n,p) = (8,41), (8,73), (8,89)).  ``max_house`` now scans a uniform grid
of [0,n] (both endpoints included) plus the known-feasible true period height M, and only
refines upward inside the grid cell above the largest feasible sample.  Every returned value
passed the (floating, tolerance-based) feasibility test or is the known witness M, so it is a
numerical LOWER estimate of the relaxation sup that is always >= M; feasible islands narrower
than the grid spacing above it can be missed, so it is not a certified upper bound on the
house.  Rows where the numerical test rejected the true period measure are flagged.
"""
import numpy as np
from numpy.polynomial import polynomial as npp

def is_prime(x):
    if x < 2: return False
    for q in range(2, int(x**0.5)+1):
        if x % q == 0: return False
    return True

def find_prime(target, n):
    # prime p ~ target with p = 1 mod n
    k = target // n
    for dk in range(0, 100000):
        for kk in (k+dk, k-dk):
            p = kk*n + 1
            if p > n*n and is_prime(p):
                return p
    raise RuntimeError

def primitive_root(p):
    fac = []
    x = p-1
    d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def period_values(p, n):
    """distinct Gauss-period values, longdouble; coset reps g^j, j=0..m-1."""
    g = primitive_root(p)
    m = (p-1)//n
    gm = pow(g, m, p)          # generator of mu_n
    mun = np.array([pow(gm, k, p) for k in range(n)], dtype=np.int64)
    # v_j = sum_{x in mu_n} cos(2 pi (g^j x mod p) / p)   (real since -1 in mu_n for even n)
    reps = np.empty(m, dtype=np.int64)
    r = 1
    for j in range(m):
        reps[j] = r
        r = (r*g) % p
    vals = np.empty(m, dtype=np.longdouble)
    tp = 2.0*np.pi/p
    for j in range(m):
        idx = (reps[j]*mun) % p
        vals[j] = np.cos(tp*idx.astype(np.longdouble)).sum()
    return vals

def hankel_feasible(mom_scaled, D, tol=1e-11):
    """mom_scaled[r] = mu_r / n^r (normalized measure moments, r=0..D, D even).
    Hausdorff feasibility on [-1,1]: H_k = [mu_{i+j}] psd (i,j<=k) and
    [mu_{i+j} - mu_{i+j+2}] psd (i,j<=k-1), 2k = D."""
    k = D//2
    H1 = np.array([[mom_scaled[i+j] for j in range(k+1)] for i in range(k+1)], dtype=float)
    H2 = np.array([[mom_scaled[i+j] - mom_scaled[i+j+2] for j in range(k)] for i in range(k)], dtype=float)
    e1 = np.linalg.eigvalsh(H1)
    e2 = np.linalg.eigvalsh(H2) if k >= 1 else np.array([1.0])
    s1 = max(abs(e1).max(), 1e-30); s2 = max(abs(e2).max(), 1e-30)
    return e1.min() >= -tol*s1 and e2.min() >= -tol*s2

def scan_max_feasible(feas, n, grid=4000, known=(), refine=60):
    """Largest spike height in [0, n] accepted by ``feas``, found WITHOUT assuming the
    feasible set is an interval.

    Samples the uniform grid {k n / grid : k = 0..grid} (both endpoints included) together
    with the heights in ``known``; takes the largest accepted sample h; then bisects only
    inside the grid cell (h, next grid point], keeping the lower end accepted.  The result is
    therefore always an accepted height, i.e. a lower estimate of the true sup; feasible
    islands narrower than n/grid above it can be missed.  Returns (best, accepted_known)
    where best is None if no sample is accepted and accepted_known lists which ``known``
    heights passed.
    """
    n = float(n)
    samples = sorted({n * k / grid for k in range(grid + 1)} |
                     {min(max(float(abs(h)), 0.0), n) for h in known})
    accepted = [h for h in samples if feas(h)]
    accepted_known = [h for h in known if feas(min(float(abs(h)), n))]
    if not accepted:
        return None, accepted_known
    lo = accepted[-1]
    above = [h for h in samples if h > lo]
    if above:
        hi = above[0]
        for _ in range(refine):
            mid = 0.5 * (lo + hi)
            if feas(mid):
                lo = mid
            else:
                hi = mid
    return lo, accepted_known


def max_house(P, m, n, D, grid=4000, known=()):
    """Numerical estimate of sup H such that a unit spike at +-H plus a bulk of mass m-1
    supported on [-n,n] matches moments P_r, r=1..D (bulk moments P_r - (+-H)^r).

    Uses ``scan_max_feasible`` (grid scan, no monotonicity assumption).  ``known`` are heights
    of measures known to be feasible (e.g. the true period house M); the returned value is
    max(scan result, known heights), so it never falls below a known witness.  Returns
    (value, known_rejected) where known_rejected lists known witnesses the floating
    feasibility test rejected (a tolerance artefact to be flagged, not a refutation).
    """
    def feas1(H):
        mus = np.empty(D+1, dtype=np.longdouble)
        mus[0] = 1.0
        Hs = np.longdouble(H)
        for r in range(1, D+1):
            mus[r] = (P[r] - Hs**r) / ((m-1) * np.longdouble(n)**r)
        return hankel_feasible(mus, D)
    def feas(H):
        # the house allows the spike on either side
        return feas1(H) or feas1(-H)
    best, accepted_known = scan_max_feasible(feas, n, grid=grid, known=known)
    rejected = [h for h in known if h not in accepted_known]
    value = max([best if best is not None else 0.0] + [float(abs(h)) for h in known])
    return value, rejected

def run(n, p, Dmax=None, label=""):
    m = (p-1)//n
    vals = period_values(p, n)
    M = float(np.abs(vals).max())
    target = float(np.sqrt(n*np.log(p/n)))
    if Dmax is None:
        Dmax = int(2*np.log2(m)) + 6
    P = np.empty(Dmax+1, dtype=np.longdouble)
    for r in range(Dmax+1):
        P[r] = np.sum(vals**r)
    # sanity: P1 ~ -1, P2 ~ p-n
    print(f"\n### n={n} p={p} m={m} {label}")
    print(f"sanity: P1={float(P[1]):+.6f} (expect -1)   P2={float(P[2]):.4f} (expect {p-n})   "
          f"P3={float(P[3]):.2f} (expect -n^2={-n*n} if N0(3)=0)")
    print(f"true M = {M:.4f}   sqrt(n log(p/n)) = {target:.4f}   trivial cap n = {n}   M/target = {M/target:.3f}")
    print("maxhouse(D): grid-scan lower estimate of the relaxation sup, floored at the known")
    print("feasible period height M (numerical diagnostic, not a certified upper bound)")
    print(f"{'D':>4} {'maxhouse(D)':>12} {'ladder':>12} {'mh/target':>10} {'mh/M':>8}")
    rows = []
    Dstar_target = None; Dstar_M = None
    for D in range(2, Dmax+1, 2):
        mh, rejected = max_house(P, m, n, D, known=(M,))
        ladder = min(float(P[2*r])**(1.0/(2*r)) for r in range(1, D//2+1))
        flag = "  [true period measure rejected numerically]" if rejected else ""
        print(f"{D:>4} {mh:>12.4f} {ladder:>12.4f} {mh/target:>10.3f} {mh/M:>8.3f}{flag}")
        rows.append((D, mh, ladder))
        if Dstar_target is None and mh <= 2*target: Dstar_target = D
        if Dstar_M is None and mh <= 1.05*M: Dstar_M = D
    print(f"D*(mh<=2*sqrt(n log(p/n))) = {Dstar_target}   D*(mh<=1.05*M) = {Dstar_M}   "
          f"2*log2(m) = {2*np.log2(m):.1f}")
    print("(D* values use the grid-scan lower estimate; a missed narrow feasible island would")
    print(" only raise maxhouse(D), so they are optimistic, not certified.)")
    return rows

if __name__ == "__main__":
    # prize-representative beta=4 primes
    for n, tgt in [(8, 8**4), (16, 16**4), (32, 32**4)]:
        p = find_prime(tgt, n)
        run(n, p, label=f"(beta=4 shape, p~n^4)")
    # small-m instances for the integrality lane
    for n, p in [(8, 41), (8, 73), (8, 89), (8, 233)]:
        assert is_prime(p) and (p-1) % n == 0
        run(n, p, label="(small-m, integrality lane)")
