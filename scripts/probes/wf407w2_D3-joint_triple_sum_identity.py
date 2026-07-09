#!/usr/bin/env python3
# wf407-w2 / D3-joint : the EXACT algebraic identity for the off-diagonal joint
# moments as Gauss/Jacobi TRIPLE/QUAD-product sums, and the decisive test:
# do they reduce to the SAME single-frequency wall B = max|eta_b|, or are they a
# separate object that Weil/Hasse-Davenport bounds nontrivially?
#
# KEY ALGEBRA.  Let eta_c = sum_{y in mu_n} zeta^{g^c y}.  The UNCENTERED joint
# moment over ALL c (not distinct yet) is the "spectral sum":
#   P_r := sum_{c=0}^{m-1} eta_c^r .
# Because the cosets g^c mu_n partition F_p^* , and eta is a class function on
# cosets, P_r relates to a FULL character sum.  Precisely, for the r-th power-sum
# of the periods, with N_r(s) = #{(y_1..y_r) in mu_n^r : sum_i g^{c} y_i = s},
#   eta_c^r = sum_s N_r^{(c)}(s) zeta^s ,
# and summing over the m cosets c (i.e. over the full orbit of mu_n under F_p^*/mu_n)
# turns the coset index into a dilation.  The CENTERED distinct-tuple moment is then
# a signed combination of power-sums P_1, P_2, ... (Newton), so it is EXACTLY a
# linear combination of FULL Gauss-type sums.  We make this concrete and check:
#
#   (A) P_r = sum_c eta_c^r  -- compute exactly; express via additive-energy-type
#       counts T_r = #{(y_1..y_r) in mu_n^r : y_1+...+y_r congruent across cosets}.
#       Verify P_2 = (p - n) + n^2/... etc (the second-moment law including c with
#       all m cosets), P_3, P_4.
#   (B) The off-diagonal CENTERED 3rd moment OFF3 = (P~3)/(m(m-1)(m-2)) where
#       P~3 = (sum cen)^3 - 3 (sum cen)(sum cen^2) + 2 sum cen^3.  Since sum cen = 0,
#       OFF3 * m(m-1)(m-2) = 2 * sum_c cen_c^3.  So the off-diagonal 3rd joint
#       moment is, up to the centering shift, governed by sum_c eta_c^3 = the
#       Gauss TRIPLE sum.  We test: is sum_c eta_c^3 of size m * (typical eta)^3
#       (=> dominated by the bulk, near-independent) or m * B^3 (=> the SAME wall)?
#   (C) Compare |sum_c eta_c^3| against m * v^1.5 (bulk scale) and against B^3
#       (single worst period cubed = the wall scale).  Decisive: which scale wins?

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
    raise RuntimeError("no primitive root")


def gauss_periods(p, n, prec=60):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    base = pow(g, m, p)
    mu = [pow(base, j, p) for j in range(n)]
    cosets = [[(pow(g, c, p) * y) % p for y in mu] for c in range(m)]
    mpmath.mp.dps = prec
    two_pi = 2 * mpmath.pi
    def zeta(k):
        ang = two_pi * (k % p) / p
        return mpmath.mpc(mpmath.cos(ang), mpmath.sin(ang))
    periods = [sum((zeta(y) for y in cosets[c]), mpmath.mpc(0)) for c in range(m)]
    return m, periods, g, mu


def main():
    cases = [
        (8, [73, 113, 241, 257, 577, 1009, 4129, 8009]),
        (16, [193, 241, 1009, 4129, 65537]),
        (32, [1153, 2081, 4129, 65537]),
        (64, [1153, 8129, 65537]),
    ]
    print("Test: is the Gauss TRIPLE sum  S3 := |sum_c eta_c^3|  of BULK scale")
    print("(~ m^{1/2} * v^{3/2}, near-independent CLT) or WALL scale (~ B^3)?")
    print()
    hdr = (f"{'n':>4} {'p':>8} {'m':>6} {'v':>9} {'B':>9} "
           f"{'|S3|':>11} {'|S3|/(m^.5 v^1.5)':>17} {'|S3|/B^3':>10} "
           f"{'B/sqrt(n)':>9} {'B/sqrt(nlogm)':>13}")
    print(hdr)
    for n, primes in cases:
        for p in primes:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 4:
                continue
            prec = 55 if p < 5000 else 45
            mm, periods, g, mu = gauss_periods(p, n, prec=prec)
            # use Re parts (periods are real iff -1 in mu_n; else use complex modulus
            # for B, but the EVT sample is Re).
            x = [pp.real for pp in periods]
            mean = sum(x) / m
            cen = [xi - mean for xi in x]
            v = float(sum(ci * ci for ci in cen) / m)
            B = float(max(abs(pp) for pp in periods))  # worst |eta_c| = the wall
            # Gauss triple sum on centered Re parts:
            S3 = sum(ci ** 3 for ci in cen)
            S3 = float(S3)
            bulk_scale = (m ** 0.5) * (v ** 1.5)
            wall_scale = B ** 3
            r_bulk = abs(S3) / bulk_scale if bulk_scale > 0 else float("nan")
            r_wall = abs(S3) / wall_scale if wall_scale > 0 else float("nan")
            B_over_sqrtn = B / math.sqrt(n)
            B_over_sqrtnlogm = B / math.sqrt(n * math.log(m)) if m > 1 else float("nan")
            print(f"{n:>4} {p:>8} {m:>6} {v:>9.3f} {B:>9.4f} "
                  f"{abs(S3):>11.4e} {r_bulk:>17.4f} {r_wall:>10.4f} "
                  f"{B_over_sqrtn:>9.4f} {B_over_sqrtnlogm:>13.4f}")
    print()
    print("INTERPRETATION")
    print(" |S3|/(m^.5 v^1.5) ~ O(1)  => triple sum is BULK/CLT scale (near-indep,")
    print("                              3rd joint moment REACHABLE for EVT).")
    print(" |S3|/B^3 ~ O(1) and >> the bulk ratio => dominated by worst period =>")
    print("                              SAME wall.  (Decisive comparison.)")


if __name__ == "__main__":
    main()
