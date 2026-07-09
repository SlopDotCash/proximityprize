#!/usr/bin/env python3
"""
#407 dense-cayley-spectral, STRONGEST FORM: the Krein / association-scheme angle.

The cyclotomic association scheme: vertices F_q, relation R_i = {(x,y): (x-y) in coset c_i mu_n}.
This is a commutative m-class association scheme (m=(q-1)/n classes). Its eigenmatrix P has
entries = Gauss periods. B = max|eta| are the eigenvalues. Krein conditions (dual eigenvalue
positivity) are an SDP-positivity lever the bare Alon-Boppana/trace bound does not use.

QUESTION: do the Krein conditions FORCE max|eta| <= C sqrt(n log m)?
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def cyclotomic_scheme(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    cosets = []
    for i in range(m):
        coset = [pow(g, i + m * j, p) for j in range(n)]
        cosets.append(coset)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    P = np.zeros((m, m), dtype=complex)
    for k in range(m):
        gk = pow(g, k, p)
        for i in range(m):
            P[k, i] = sum(w[(gk * x) % p] for x in cosets[i])
    mult = np.zeros(m)
    for k in range(m):
        denom = sum((abs(P[k, i]) ** 2) / n for i in range(m))
        mult[k] = p / denom if denom > 0 else 0
    return P, mult


print("=" * 100)
print(" KREIN / CYCLOTOMIC-SCHEME angle: do scheme-positivity constraints bound B = max|eta|?")
print("=" * 100)
for n in [4, 6, 8]:
    for m in [4, 6, 8, 10, 14]:
        p = m * n + 1
        if not isprime(p):
            continue
        P, mult = cyclotomic_scheme(p, n)
        offdiag = np.abs(P[1:, :])
        B = offdiag.max()
        mult_int_err = np.max(np.abs(mult - np.round(mult)))
        print(f" n={n} m={m} p={p}: B={B:.3f}  sqrt(n*lnm)={math.sqrt(n*math.log(m)):.3f}  "
              f"B/sqrt(nlnm)={B/math.sqrt(n*math.log(m)):.3f}  mult_int_err={mult_int_err:.2e}")
print()
print("KEY POINT: Krein params of the cyclotomic scheme are POLYNOMIALS in the Gauss periods")
print("(structure constants of the Bose-Mesner algebra), AUTOMATICALLY >=0 for the actual scheme.")
print("So Krein positivity is a CONSEQUENCE of the true eta, not an a-priori constraint. Every")
print("eta-vector satisfying the row/col Parseval sum rules + multiplicity integrality is")
print("scheme-feasible -- and those rules are exactly the MOMENT constraints already walled.")
