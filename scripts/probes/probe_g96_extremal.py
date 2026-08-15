#!/usr/bin/env python3
"""G96 probe A: the constrained extremal problem for the house of Gauss periods.

For real primes p, n | p-1, mu_n = n-th roots of unity in F_p^x:
  - compute the m = (p-1)/n distinct period values v_1..v_m exactly-enough (longdouble),
  - compute true power sums P_r = sum v^r (r <= Dmax),
  - solve max-house(D) = sup { max|v| : real measure of mass m on [-n,n], moments P_1..P_D }
    via Hankel PSD feasibility + binary search on the spike height H,
  - compare vs true M, sqrt(n log(p/n)), and the moment ladder min_{2r<=D} P_{2r}^{1/2r}.
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

def max_house(P, m, n, D):
    """sup H such that measure with mass m-? : spike at H plus bulk of mass m-1 matching
    moments P_r - H^r, r=1..D, supported on [-n,n]."""
    lo, hi = 0.0, float(n)
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
    if feas(hi - 1e-9*hi):
        return hi
    for _ in range(80):
        mid = 0.5*(lo+hi)
        if feas(mid): lo = mid
        else: hi = mid
    return lo

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
    print(f"{'D':>4} {'maxhouse(D)':>12} {'ladder':>12} {'mh/target':>10} {'mh/M':>8}")
    rows = []
    Dstar_target = None; Dstar_M = None
    for D in range(2, Dmax+1, 2):
        mh = max_house(P, m, n, D)
        ladder = min(float(P[2*r])**(1.0/(2*r)) for r in range(1, D//2+1))
        print(f"{D:>4} {mh:>12.4f} {ladder:>12.4f} {mh/target:>10.3f} {mh/M:>8.3f}")
        rows.append((D, mh, ladder))
        if Dstar_target is None and mh <= 2*target: Dstar_target = D
        if Dstar_M is None and mh <= 1.05*M: Dstar_M = D
    print(f"D*(mh<=2*sqrt(n log(p/n))) = {Dstar_target}   D*(mh<=1.05*M) = {Dstar_M}   "
          f"2*log2(m) = {2*np.log2(m):.1f}")
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
