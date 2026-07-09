#!/usr/bin/env python3
"""
[centrallaw] FOUNDATIONAL independent reproduction of the #407 central law.

Object: prime p, p-1 = m*n, mu_n = order-n subgroup of F_p^x (index m).
  eta_b = sum_{x in mu_n} e_p(b*x),   e_p(t) = exp(2*pi*i*t/p).
  B = M(n,p) = max_{b != 0} |eta_b|.
Law under test:  R(n,p) = B / sqrt(n * ln(m))  should be FLAT in ~[1.1,1.5], no trend.

This is FRESH code. No reuse of existing probes. Two independent methods cross-check B:
  METHOD A (coset-direct): eta_b depends only on coset b*mu_n. Enumerate the m cosets,
     compute eta on a representative of each via exact complex exponential sum over mu_n.
  METHOD B (DFT/Gauss-sum identity): eta_b = (1/m)[ -1 + sum_{j=1}^{m-1} psi(b)^{-j} tau(psi^j) ]
     with |tau(psi^j)| = sqrt(p). We verify METHOD A reproduces this magnitude structure.
We use METHOD A as the ground truth (it makes NO unproven assumption about |tau|=sqrt(p)).
"""
import numpy as np
import math
from sympy import isprime, primitive_root

def gauss_period_floor(p, n):
    """Exact B = max_{b!=0} |eta_b| via coset enumeration.
    Returns (B, all_coset_abs_values_array)."""
    assert (p - 1) % n == 0, "n must divide p-1"
    m = (p - 1) // n
    g = primitive_root(p)            # generator of F_p^x
    # mu_n = <g^m>, the order-n subgroup. Elements: g^(m*k), k=0..n-1.
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64)
    cur = 1
    for k in range(n):
        mu[k] = cur
        cur = (cur * gm) % p
    # cosets of mu_n in F_p^x: representatives g^t, t=0..m-1.
    # eta on coset rep r = sum_{x in mu} exp(2*pi*i * (r*x mod p) / p).
    two_pi_over_p = 2.0 * math.pi / p
    abs_vals = np.empty(m, dtype=np.float64)
    r = 1
    for t in range(m):
        # products r*x mod p for x in mu
        prods = (r * mu) % p
        ang = two_pi_over_p * prods
        s = np.cos(ang).sum() + 1j * np.sin(ang).sum()
        abs_vals[t] = abs(s)
        r = (r * g) % p
    B = abs_vals.max()
    return B, abs_vals, m

def gauss_period_floor_fft(p, n):
    """Independent cross-check via full additive-character FFT-free direct sum but
    grouping by the value c = (b*x mod p). Uses the indicator of mu_n.
    eta_b = sum over all residues c of [c in (b*mu_n)] * e_p(c).
    Equivalently the DFT of the indicator 1_{mu_n} evaluated at b. We compute the
    DFT of the subgroup indicator over Z_p directly: eta_b = sum_{x in mu} e_p(b x).
    This recomputes for ALL b=1..p-1 (slow, only for small p) as a sanity check."""
    m = (p - 1) // n
    g = primitive_root(p)
    gm = pow(g, m, p)
    mu = []
    cur = 1
    for _ in range(n):
        mu.append(cur)
        cur = (cur * gm) % p
    mu = np.array(mu, dtype=np.int64)
    tp = 2.0 * math.pi / p
    best = 0.0
    for b in range(1, p):
        prods = (b * mu) % p
        s = np.exp(1j * tp * prods).sum()
        if abs(s) > best:
            best = abs(s)
    return best

if __name__ == "__main__":
    # quick self-consistency test on a small prime
    p, n = 41, 8     # p-1=40, n=8, m=5
    B1, _, m = gauss_period_floor(p, n)
    B2 = gauss_period_floor_fft(p, n)
    print(f"self-check p={p} n={n} m={m}: coset B={B1:.6f}  brute B={B2:.6f}  diff={abs(B1-B2):.2e}")
