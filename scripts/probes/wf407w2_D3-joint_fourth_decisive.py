#!/usr/bin/env python3
# wf407-w2 / D3-joint : the DECISIVE 4th-moment test.
#
# Established (powersum_exact.py):  P_3 = sum_c eta_c^3 = -n^2 EXACTLY (closed form,
# m-independent, A_3(0)=0).  So the 3rd JOINT moment is REACHABLE (known exactly).
#
# The 4th is the wall candidate.  P_4 = sum_c eta_c^4 = A_4(0) - a_4.  We test whether
# P_4 has a CLOSED FORM in (n,m,p) [=> reachable] or carries a defect tied to the
# additive energy / B(mu_n) wall [=> walled].
#
# DECOMPOSITION OF THE EVT-RELEVANT QUANTITY.  The de Finetti / EVT 4th joint moment
# is the off-diagonal centered avg off4 = avg_{a,b,c,d distinct} prod(eta-mean).
# Newton => off4 * m(m-1)(m-2)(m-3) = 3 S2^2 - 6 S4   (since S1 = 0),
#   where S2 = sum cen_c^2 = m v,  S4 = sum cen_c^4.
# So off4 is governed by S4 = sum_c (eta_c - mean)^4, i.e. by the 4th DIAGONAL
# power-sum.  The EVT floor needs off4 ~ 3 v^2 (Gaussian); i.e. needs
#   S4 = sum_c cen_c^4 ~ 3 m v^2 * (1 + o(1))   [the Gaussian kurtosis identity].
# A heavy upper tail (one big period B) makes S4 ~ B^4, which for B ~ sqrt(n log m)
# gives S4 ~ n^2 log^2 m -- comparable to 3 m v^2 ~ 3 m n^2/4 only if log^2 m << m
# (true).  So the BINDING quantity for the 4th moment is the kurtosis
#   kappa4 = S4/(m v^2) - 3   (excess kurtosis of the period SAMPLE).
# kappa4 -> 0  <=>  4th moment Gaussian <=> EVT floor 4th-order-reachable.
# kappa4 bounded but nonzero, or growing, localizes the wall.
#
# We compute kappa4 exactly and check its scaling vs the deep-moment wall.

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


def periods_of(p, n, prec=55):
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


def main():
    cases = [
        (8, [73, 89, 113, 137, 233, 241, 257, 401, 577, 1009, 2017, 4129, 8009]),
        (16, [97, 113, 193, 241, 257, 353, 1009, 2017, 4129, 8081, 65537]),
        (32, [193, 257, 353, 1153, 2081, 4129, 8161, 65537]),
        (64, [257, 449, 641, 1153, 1217, 8129, 65537]),
    ]
    print("4th-moment / kurtosis decisive test.  Re parts of the m periods.")
    print("kappa4 = S4/(m v^2) - 3  (excess kurtosis); -> 0 => 4th joint moment")
    print("Gaussian (EVT-reachable).  Also B and the deep-moment wall comparison.")
    print()
    print(f"{'n':>4}{'p':>8}{'m':>7}{'v':>9}{'B':>9}{'kappa4':>11}"
          f"{'S4/(3mv^2)':>12}{'B^4/S4':>9}{'B/sqrt(nlnm)':>13}{'note':>8}")
    for n, primes in cases:
        for p in primes:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 4:
                continue
            prec = 55 if p < 5000 else 45
            mm, periods = periods_of(p, n, prec=prec)
            x = [pp.real for pp in periods]
            mean = sum(x) / m
            cen = [xi - mean for xi in x]
            v = float(sum(c * c for c in cen) / m)
            S4 = float(sum(c ** 4 for c in cen))
            B = float(max(abs(pp) for pp in periods))
            kappa4 = S4 / (m * v ** 2) - 3.0 if v > 0 else float("nan")
            ratio = S4 / (3.0 * m * v ** 2) if v > 0 else float("nan")
            B4_over_S4 = (B ** 4) / S4 if S4 > 0 else float("nan")
            Bnlm = B / math.sqrt(n * math.log(m)) if m > 1 else float("nan")
            # dyadic-tower / Fermat anomaly note
            note = ""
            if (p - 1) & (p - 2) == 0:  # p-1 is power of 2 => fully dyadic
                note = "DYADIC"
            print(f"{n:>4}{p:>8}{m:>7}{v:>9.3f}{B:>9.4f}{kappa4:>11.4f}"
                  f"{ratio:>12.5f}{B4_over_S4:>9.4f}{Bnlm:>13.4f}{note:>8}")
    print()
    print("READ: kappa4 -> 0 with m  => 4th moment is asymptotically Gaussian =>")
    print("the de Finetti/EVT 4th joint moment is REACHABLE (no 4th-order wall).")
    print("kappa4 stuck at O(1) (esp. DYADIC rows) => 4th moment carries the defect")
    print("= the deep-moment / additive-energy wall (walled).")


if __name__ == "__main__":
    main()
