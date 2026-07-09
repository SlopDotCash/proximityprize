#!/usr/bin/env python3
# wf407-w2 / D3-joint : EXACT identification of the period power-sums P_r = sum_c eta_c^r
# as additive-coincidence counts (Jacobi/Gauss r-fold sums), in CLOSED FORM.
#
# CLAIM TO TEST.  P_r = sum_{c=0}^{m-1} eta_c^r is an EXACT INTEGER (a class number /
# coincidence count), NOT a transcendental, because:
#   sum_c eta_c^r = sum_c (sum_{y in g^c mu_n} zeta^y)^r
#                 = sum_c sum_{y_1..y_r in g^c mu_n} zeta^{y_1+...+y_r}.
# As c ranges over 0..m-1, the cosets g^c mu_n partition F_p^*.  So
#   sum_c [tuples from coset c] = sum over r-tuples (z_1..z_r) lying in a COMMON coset.
# Hence
#   P_r = sum_{(z_1..z_r): all in one coset of mu_n} zeta^{z_1+...+z_r}.
# Group by s = z_1+...+z_r in F_p:
#   P_r = sum_{s in F_p} A_r(s) zeta^s,  A_r(s) = #{(z_1..z_r) in (one coset)^r : sum=s}.
# By additive-character symmetry over s (the multiset {A_r(s)} is constant on F_p^*
# when the configuration is dilation-balanced), P_r = A_r(0) - (1/(p-1)) sum_{s!=0}...
# i.e. P_r = A_r(0)*1 + (sum_{s} A_r(s) zeta^s).  Since sum_s A_r(s) = m*n^r (total
# tuples) and sum_{s!=0} zeta^s = -1, IF A_r(s)=A_r(s') for all s,s'!=0 (call it a)
# then P_r = A_r(0) + a*(-1) = A_r(0) - a, and m*n^r = A_r(0) + (p-1)*a.
#
# So the DECISIVE structural quantity is  A_r(0) = #{r-tuples in a common mu_n-coset
# summing to 0}  -- a SUBGROUP-RESTRICTED r-fold additive count.  We:
#   (1) compute P_r exactly (high prec) and round to nearest integer -> confirm integer.
#   (2) compute A_r(0) directly (exact integer enumeration) and the flatness of
#       A_r(s) for s!=0; verify P_r = A_r(0) - a  when flat.
#   (3) Identify: is A_r(0) a BULK count (~ m*n^r/p, i.e. random) giving P_r small,
#       or does it carry an O(n^r) anomaly = the SAME additive-energy defect wall?
#
# This pins WHICH object the 3rd/4th joint moment IS.

import math
import mpmath
import sympy as sp
from collections import Counter


def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    fs = sp.factorint(phi)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fs):
            return g
    raise RuntimeError("no primitive root")


def subgroup_and_cosets(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    base = pow(g, m, p)
    mu = [pow(base, j, p) for j in range(n)]
    coset_of = {}  # element -> coset index
    for c in range(m):
        gc = pow(g, c, p)
        for y in mu:
            coset_of[(gc * y) % p] = c
    return g, m, mu, coset_of


def Ar0_and_flatness(p, n, r, coset_of, mu, g, m):
    """A_r(s) = # r-tuples (z_1..z_r), all in a COMMON coset, with sum = s.
    Enumerate by: for each coset c, count r-tuples from coset c by their sum.
    Then A_r(s) = sum_c (count of r-tuples in coset c summing to s).
    For r<=4 and small n this is enumerable as a convolution of the coset's
    additive-indicator with itself r times."""
    # build coset element lists
    cosets = [[] for _ in range(m)]
    for z, c in coset_of.items():
        cosets[c].append(z)
    # For each coset, the count-of-pairs/triples by sum is the r-fold additive
    # convolution of its indicator over Z_p.  Sum over cosets.
    A = [0] * p
    for c in range(m):
        # r-fold convolution of indicator of cosets[c]
        ind = [0] * p
        for z in cosets[c]:
            ind[z] += 1
        conv = ind
        for _ in range(r - 1):
            newc = [0] * p
            for a in range(p):
                ca = conv[a]
                if ca == 0:
                    continue
                for z in cosets[c]:
                    newc[(a + z) % p] += ca
            conv = newc
        for s in range(p):
            A[s] += conv[s]
    A0 = A[0]
    # flatness of A[s] for s != 0
    vals = Counter(A[s] for s in range(1, p))
    flat = (len(vals) == 1)
    a_nonzero = next(iter(vals)) if flat else None
    return A0, flat, a_nonzero, vals


def Pr_highprec(p, n, r, prec=70):
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
    periods = [sum((zeta(y) for y in cosets[c]), mpmath.mpc(0)) for c in range(m)]
    P = {}
    for r in (1, 2, 3, 4):
        P[r] = sum((e ** r for e in periods), mpmath.mpc(0))
    return P, periods


def main():
    cases = [
        (8, [73, 113, 241, 257, 577]),
        (16, [193, 241, 1009]),
        (32, [1153, 2081]),
        (4, [13, 29, 37, 41, 53, 61, 257]),  # small n for full A_r(0) clarity
    ]
    print("Exact identification of period power-sums P_r = sum_c eta_c^r.")
    print("P_r should be a real INTEGER; P_r = A_r(0) - a (flat case).")
    print("BULK prediction (full near-independence): A_r(0) ~ m*n^r/p (random sum=0).")
    print()
    for n, primes in cases:
        print(f"---- n={n} ----")
        for p in primes:
            if (p - 1) % n != 0:
                continue
            m = (p - 1) // n
            if m < 2:
                continue
            g, mm, mu, coset_of = subgroup_and_cosets(p, n)
            P, periods = Pr_highprec(p, n, 4, prec=60 if p < 2000 else 50)
            line = f"n={n} p={p:>6} m={m:>5}:"
            for r in (2, 3, 4):
                Pr = P[r]
                Pr_re = float(Pr.real)
                Pr_im = float(Pr.imag)
                Pr_round = round(Pr_re)
                A0, flat, a_nz, vals = Ar0_and_flatness(p, n, r, coset_of, mu, g, m)
                pred_A0 = m * (n ** r) / p
                # check P_r = A0 - a (flat) ; sum check m*n^r = A0 + (p-1)*a
                if flat:
                    Pr_from_count = A0 - a_nz
                    sumchk = (A0 + (p - 1) * a_nz == m * (n ** r))
                else:
                    # general: P_r = sum_s A[s] zeta^s ; cannot collapse, but A0 still meaningful
                    Pr_from_count = None
                    sumchk = None
                anomaly = A0 - pred_A0  # excess over random
                line += (f"\n   r={r}: P_r={Pr_round:>8} (im={Pr_im:+.1e}) "
                         f"A_{r}(0)={A0:>7} pred~{pred_A0:>10.3f} "
                         f"anomaly(A0-pred)={anomaly:>+10.3f} "
                         f"flat={flat} a={a_nz} "
                         f"P=A0-a?{'OK' if (flat and Pr_from_count==Pr_round) else ('-' if flat else 'NONFLAT')} "
                         f"sumchk={sumchk}")
            print(line)
        print()


if __name__ == "__main__":
    main()
