#!/usr/bin/env python3
# wf407-w2 / D3-joint : isolate the DYADIC TOWER (prize-shape) and decide whether
# the 4th joint moment converges to Gaussian (reachable) or carries a growing defect
# (= the deep-moment / additive-energy wall).
#
# Prize regime: n = 2^mu smooth, p = n*2^128 + 1 (so p-1 = 2^(mu+128), FULLY dyadic),
# m = (p-1)/n = 2^128.  We cannot reach m=2^128 numerically, but we CAN scan the
# dyadic family p = n*2^t + 1 (prime) for growing t (= tower depth) at fixed n, and
# watch whether the 4th joint cumulant (excess kurtosis kappa4) of the period sample:
#   - decays to 0 with t  => 4th joint moment ASYMPTOTICALLY GAUSSIAN, EVT-reachable;
#   - stays O(1) / grows  => carries the deep-moment defect = SAME wall.
#
# We also separate the GENERIC family (p with p-1 having an ODD cofactor, i.e. NOT
# fully dyadic) at matched m, to confirm the dyadic excess is the structured one.

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


def stats(p, n):
    m, periods = periods_of(p, n)
    x = [pp.real for pp in periods]
    mean = sum(x) / m
    cen = [xi - mean for xi in x]
    v = float(sum(c * c for c in cen) / m)
    S3 = float(sum(c ** 3 for c in cen))
    S4 = float(sum(c ** 4 for c in cen))
    B = float(max(abs(pp) for pp in periods))
    kappa4 = S4 / (m * v ** 2) - 3.0 if v > 0 else float("nan")
    # off-diagonal centered 3rd and 4th joint moments
    off3 = (2 * S3) / (m * (m - 1) * (m - 2)) if m >= 3 else float("nan")
    off2 = -v / (m - 1)
    off4 = (3 * (m * v) ** 2 - 6 * S4) / (m * (m - 1) * (m - 2) * (m - 3)) if m >= 4 else float("nan")
    cum4 = off4 - 3 * off2 ** 2 if m >= 4 else float("nan")
    return dict(m=m, v=v, B=B, kappa4=kappa4, off3=off3, off2=off2,
                off4=off4, cum4=cum4, S4=S4)


def main():
    print("DYADIC TOWER (prize-shape p = n*2^t+1) vs GENERIC family.")
    print("Watch kappa4 (excess kurtosis = 4th joint cumulant scale) as t grows.")
    print()
    for n in (8, 16, 32):
        print(f"==== n = {n} ====")
        print(f"{'p':>9}{'t=v2(p-1)':>10}{'m':>9}{'v':>9}{'B':>9}"
              f"{'kappa4':>10}{'B/sqrt(nlnm)':>13}{'off3/v^1.5':>12}"
              f"{'cum4/v^2':>11}{'family':>10}")
        # collect dyadic-tower primes p = n*2^t + 1
        dy = []
        for t in range(2, 26):
            p = n * (1 << t) + 1
            if sp.isprime(p):
                dy.append((t, p))
        gen = []  # generic: p-1 has an odd cofactor > 1, n | p-1
        cand = 0
        c = 0
        for p in sp.primerange(50, 70000):
            if (p - 1) % n == 0:
                cof = (p - 1) // n
                # require an odd factor (not fully dyadic) and not in dyadic list
                if cof % 2 == 1 and cof > 1:
                    gen.append(p)
                    c += 1
                    if c >= 8:
                        break
        rows = []
        for t, p in dy:
            if p > 70000:
                continue
            s = stats(p, n)
            rows.append((p, t, s, "DYADIC"))
        for p in gen:
            t = (p - 1 & -(p - 1)).bit_length() - 1
            s = stats(p, n)
            rows.append((p, t, s, "generic"))
        rows.sort(key=lambda r: r[2]["m"])
        for p, t, s, fam in rows:
            Bnlm = s["B"] / math.sqrt(n * math.log(s["m"])) if s["m"] > 1 else float("nan")
            o3 = s["off3"] / (s["v"] ** 1.5) if s["v"] > 0 else float("nan")
            c4 = s["cum4"] / (s["v"] ** 2) if s["v"] > 0 else float("nan")
            print(f"{p:>9}{t:>10}{s['m']:>9}{s['v']:>9.3f}{s['B']:>9.3f}"
                  f"{s['kappa4']:>10.4f}{Bnlm:>13.4f}{o3:>12.3e}"
                  f"{c4:>11.3e}{fam:>10}")
        print()
    print("DECISION:")
    print(" If kappa4 (DYADIC) GROWS with t while generic kappa4 -> 0:")
    print("   the 4th joint moment carries the dyadic-tower deep-moment defect")
    print("   = SAME additive-energy/B(mu_n) wall => 4th joint moment WALLED at prize.")


if __name__ == "__main__":
    main()
