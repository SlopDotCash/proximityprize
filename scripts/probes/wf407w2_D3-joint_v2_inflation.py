#!/usr/bin/env python3
# wf407-w2 / D3-joint : does the 2-adic depth t = v2(p-1) drive the diagonal
# deep-moment inflation (B and kurtosis), holding n and m comparable?  This pins
# whether the EVT-binding object (NOT the off-diagonal joint moment, which vanishes)
# is the dyadic-tower deep-moment defect = the standing wall.
#
# For fixed n, scan many primes p with n | p-1, bucket by t = v2((p-1)/n)
# (extra 2-power depth in the COSET index beyond mu_n), and compare at comparable m:
#   B/sqrt(n ln m)  (the worst-period inflation; EVT prediction ~ 1) and
#   kappa4          (excess kurtosis; Gaussian = 0).
# A monotone increase with t = the deep-moment dyadic defect.

import math
import mpmath
import sympy as sp


def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    fs = sp.factorint(phi)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fs):
            return g
    raise RuntimeError


def periods_of(p, n, prec=45):
    g = primitive_root(p)
    m = (p - 1) // n
    base = pow(g, m, p)
    mu = [pow(base, j, p) for j in range(n)]
    cosets = [[(pow(g, c, p) * y) % p for y in mu] for c in range(m)]
    mpmath.mp.dps = prec
    two_pi = 2 * mpmath.pi
    def zeta(k):
        ang = two_pi * (k % p) / p
        return mpmath.mpc(mpmath.cos(ang), mpmath.sin(ang))
    return m, [sum((zeta(y) for y in cosets[c]), mpmath.mpc(0)) for c in range(m)]


def v2(x):
    t = 0
    while x % 2 == 0:
        x //= 2
        t += 1
    return t


def main():
    n = 16
    print(f"n={n}: B-inflation & kurtosis bucketed by 2-adic depth t=v2(m), m=(p-1)/n.")
    print("Comparable m window 50<=m<=130 to isolate the t-effect.")
    print()
    print(f"{'p':>8}{'m':>6}{'t=v2(m)':>9}{'B':>9}{'B/sqrt(nlnm)':>13}"
          f"{'kappa4':>10}{'B/sqrt(n)':>10}")
    rows = []
    for p in sp.primerange(50, 200000):
        if (p - 1) % n != 0:
            continue
        m = (p - 1) // n
        if not (50 <= m <= 140):
            continue
        t = v2(m)
        mm, periods = periods_of(p, n)
        x = [pp.real for pp in periods]
        mean = sum(x) / m
        cen = [xi - mean for xi in x]
        v = float(sum(c * c for c in cen) / m)
        S4 = float(sum(c ** 4 for c in cen))
        B = float(max(abs(pp) for pp in periods))
        kappa4 = S4 / (m * v ** 2) - 3.0
        Bnlm = B / math.sqrt(n * math.log(m))
        rows.append((t, p, m, B, Bnlm, kappa4, B / math.sqrt(n)))
    rows.sort()
    for t, p, m, B, Bnlm, k4, Bn in rows:
        print(f"{p:>8}{m:>6}{t:>9}{B:>9.3f}{Bnlm:>13.4f}{k4:>10.4f}{Bn:>10.4f}")
    # bucket averages
    print()
    print("Bucket means by t:")
    from collections import defaultdict
    buck = defaultdict(list)
    for t, p, m, B, Bnlm, k4, Bn in rows:
        buck[t].append((Bnlm, k4))
    for t in sorted(buck):
        arr = buck[t]
        mb = sum(a for a, _ in arr) / len(arr)
        mk = sum(b for _, b in arr) / len(arr)
        print(f"  t={t}: n={len(arr):>2}  mean B/sqrt(nlnm)={mb:.4f}  mean kappa4={mk:+.4f}")
    print()
    print("If mean B/sqrt(nlnm) and kappa4 INCREASE with t, the diagonal deep-moment")
    print("inflation is driven by the 2-adic tower depth = the prize wall direction.")


if __name__ == "__main__":
    main()
