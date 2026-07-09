#!/usr/bin/env python3
# wf407-w2 / D3-joint : 3rd/4th JOINT moments of distinct Gauss periods.
#
# QUESTION (T232-08 follow-up): the de Finetti / Gumbel route to the EVT floor
# B <= sqrt(2 v log m) needs the 3rd and 4th JOINT moments of DISTINCT periods
# eta_c (c = 0..m-1, m = (p-1)/n cosets) to be small ("near-independence"), so
# the period family behaves like i.i.d. Gumbel.  These joint moments EQUAL Gauss
# triple/quadruple-product sums.  Are they o(higher) (=> EVT floor reachable) or
# themselves large (=> walled)?
#
# Periods (real Gaussian periods, the Paley eigenvalues):
#   eta_c = sum_{y in coset_c} zeta_p^{y},   coset_c = g^c * mu_n,  g a primitive root.
# eta_c is real iff -1 in mu_n (n even).  We work with the real parts Re(eta_c)
# (the sample the EVT route maxes over) AND with the complex eta_c for the exact
# triple-product algebra.
#
# We compute EXACTLY (exact integer/cyclotomic where possible, else high-prec):
#   (1) the centered joint moments E_off[ prod (eta - mean) ] over DISTINCT tuples,
#       for orders r = 2,3,4, vs the per-coordinate variance v.  "Near-independence
#       to order r" <=> off-diagonal centered joint moment = o(v^{r/2} * something).
#   (2) the COMPARISON to the i.i.d. / Gaussian prediction (which is EXACTLY 0 for
#       odd off-diagonal centered moments, and 0 for the 4th off-diagonal cumulant).
#       The de Finetti route is "reachable" iff the true joint moments match these
#       to leading order; "walled" iff a structured O(1)-relative deviation persists.
#   (3) the algebraic identity: E[eta_a eta_b eta_c] (uncentered) = sum over the
#       coset structure = a Jacobi/Gauss TRIPLE sum.  We check whether it reduces to
#       the SAME incomplete-subgroup-sum object B (the standing wall) or is genuinely
#       a new, boundable Weil/Hasse-Davenport object.

import itertools
import math
import cmath

import sympy as sp
import mpmath


def primitive_root(p):
    # smallest primitive root mod p
    if p == 2:
        return 1
    phi = p - 1
    fs = sp.factorint(phi)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def gauss_periods(p, n, prec=80):
    """Return (m, periods) where periods[c] = eta_c = sum_{y in coset_c} zeta^y,
    coset_c = g^c * mu_n, mu_n the order-n subgroup.  Complex, high precision."""
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    # mu_n = <g^m>  (order n).  coset_c = g^c * mu_n, c = 0..m-1.
    base = pow(g, m, p)  # generator of mu_n
    mu = [pow(base, j, p) for j in range(n)]
    cosets = []
    for c in range(m):
        gc = pow(g, c, p)
        cosets.append([(gc * y) % p for y in mu])
    # zeta_p^k as high-prec complex
    mpmath.mp.dps = prec
    two_pi = 2 * mpmath.pi
    def zeta(k):
        ang = two_pi * (k % p) / p
        return mpmath.mpc(mpmath.cos(ang), mpmath.sin(ang))
    periods = []
    for c in range(m):
        s = mpmath.mpc(0)
        for y in cosets[c]:
            s += zeta(y)
        periods.append(s)
    return m, periods, cosets, mu


def joint_centered_moments(periods, use_real=True):
    """Compute exact-ish (high prec) per-coordinate variance v, and the AVERAGE
    over DISTINCT ordered tuples of the centered product, for r=2,3,4.
    Returns dict."""
    m = len(periods)
    if use_real:
        x = [pp.real for pp in periods]
    else:
        x = list(periods)
    mean = sum(x) / m
    cen = [xi - mean for xi in x]
    # variance (population, per coordinate)
    v = sum((ci.conjugate() * ci if not use_real else ci * ci) for ci in cen) / m
    v = v.real if hasattr(v, "real") else v

    res = {"m": m, "mean": complex(mean) if not use_real else float(mean),
           "v": float(v)}

    # order 2 off-diagonal centered: avg over a != b of cen_a * cen_b
    # = ((sum cen)^2 - sum cen^2) / (m(m-1)) = (0 - m v)/(m(m-1)) = -v/(m-1)
    S1 = sum(cen)  # = 0 by centering
    S2 = sum(ci * ci for ci in cen)
    off2 = (S1 * S1 - S2) / (m * (m - 1))
    res["off2"] = float(off2.real) if hasattr(off2, "real") else float(off2)
    res["off2_pred_-v/(m-1)"] = float(-v / (m - 1))

    # order 3 off-diagonal centered: avg over DISTINCT a,b,c of cen_a cen_b cen_c.
    # Use power-sum / Newton: sum over distinct ordered triples of c_a c_b c_c
    #   = S1^3 - 3 S1 S2 + 2 S3   (Newton's identity for e3-type ordered distinct).
    # Actually sum_{a,b,c distinct} = S1^3 - 3 S1 S2 + 2 S3.
    S3 = sum(ci ** 3 for ci in cen)
    num3 = S1 ** 3 - 3 * S1 * S2 + 2 * S3
    cnt3 = m * (m - 1) * (m - 2)
    off3 = num3 / cnt3
    res["off3"] = float(off3.real) if hasattr(off3, "real") else float(off3)
    # i.i.d./Gaussian prediction for off-diagonal centered 3rd moment = 0
    res["off3_pred_iid"] = 0.0

    # order 4 off-diagonal centered: avg over DISTINCT a,b,c,d of product.
    # sum_{a,b,c,d distinct} c_a c_b c_c c_d
    #   = S1^4 - 6 S1^2 S2 + 3 S2^2 + 8 S1 S3 - 6 S4
    S4 = sum(ci ** 4 for ci in cen)
    num4 = S1 ** 4 - 6 * S1 ** 2 * S2 + 3 * S2 ** 2 + 8 * S1 * S3 - 6 * S4
    cnt4 = m * (m - 1) * (m - 2) * (m - 3) if m >= 4 else 1
    off4 = num4 / cnt4 if m >= 4 else float("nan")
    res["off4"] = float(off4.real) if hasattr(off4, "real") and m >= 4 else (
        float(off4) if m >= 4 else float("nan"))
    # i.i.d. prediction for 4th off-diagonal centered moment of a centered family
    # with the linear constraint sum=0: leading term is 3*(off2)^2 (Gaussian
    # Wick), i.e. E[c_a c_b]E[c_c c_d]+E[c_a c_c]E[c_b c_d]+E[c_a c_d]E[c_b c_c]
    # = 3 * (off2)^2  (all pairings equal under exchangeability).
    res["off4_pred_gaussian_wick_3off2sq"] = 3.0 * res["off2"] ** 2

    # the de Finetti 4th CUMULANT (off-diagonal): off4 - 3*off2^2.  =0 for Gaussian.
    if m >= 4:
        res["off4_cumulant"] = res["off4"] - 3.0 * res["off2"] ** 2
    else:
        res["off4_cumulant"] = float("nan")
    return res


def main():
    # (n, list of primes p with n | p-1, ranging small -> prize-shaped q~n^k)
    cases = [
        (8, [17, 41, 73, 89, 113, 241, 257, 577, 1009, 4129, 8009]),
        (16, [17, 97, 113, 193, 241, 257, 1009, 4129, 65537]),
        (32, [97, 193, 257, 1153, 2081, 4129, 65537]),
        (64, [193, 257, 449, 641, 1153, 8129, 65537]),
    ]
    for n, primes in cases:
        print(f"\n================ n = {n} ================")
        print(f"{'p':>8} {'m':>6} {'v':>10} {'off2':>12} {'off3':>12} "
              f"{'off3/v^1.5':>11} {'off4':>12} {'off4/3off2^2':>12} "
              f"{'cum4/v^2':>11}")
        for p in primes:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 4:
                continue
            prec = 60 if p < 2000 else (50 if p < 20000 else 45)
            _, periods, cosets, mu = gauss_periods(p, n, prec=prec)
            r = joint_centered_moments(periods, use_real=True)
            v = r["v"]
            off3 = r["off3"]
            off4 = r["off4"]
            off3_norm = off3 / (v ** 1.5) if v > 0 else float("nan")
            off4_ratio = off4 / r["off4_pred_gaussian_wick_3off2sq"] if r[
                "off4_pred_gaussian_wick_3off2sq"] != 0 else float("nan")
            cum4_norm = r["off4_cumulant"] / (v ** 2) if v > 0 else float("nan")
            print(f"{p:>8} {m:>6} {v:>10.4f} {off3:>12.4e} {off3:>12.4e} "
                  f"{off3_norm:>11.4e} {off4:>12.4e} {off4_ratio:>12.6f} "
                  f"{cum4_norm:>11.4e}")
    print()
    print("LEGEND")
    print(" off2 = avg over distinct a!=b of (eta_a-mean)(eta_b-mean), Re parts")
    print("       (must equal -v/(m-1) EXACTLY = the vacuous covariance fingerprint)")
    print(" off3 = avg over distinct a,b,c of product of centered Re periods")
    print("       i.i.d./Gaussian prediction = 0.  off3/v^1.5 = relative size vs the")
    print("       natural scale; if -> 0, near-independence holds to 3rd order.")
    print(" off4 = avg over distinct a,b,c,d ; Gaussian (Wick) prediction = 3*off2^2")
    print(" off4/3off2^2 -> 1 means 4th joint moment matches Gaussian (reachable)")
    print(" cum4/v^2 = (off4 - 3 off2^2)/v^2 = the 4th joint CUMULANT, =0 for Gaussian")


if __name__ == "__main__":
    main()
