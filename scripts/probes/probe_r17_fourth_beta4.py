#!/usr/bin/env python3
"""R17 (c): fourth moment S4 = sum_{s0} |T_chi(s0)|^4 at beta~4 vs Wick.
Wick(complex chi) = 2 p n^2 ; Wick(real chi=Legendre) = 3 p n^2.
Also diagonal-pairing exact main term: complex: (2n^2 - n) * (p - O), track ratio.
Error heuristic: n^4 sqrt(p) / (p n^2) = n^2/sqrt(p) = n^{2 - beta/2}."""
import numpy as np
from sympy import isprime, primitive_root, n_order

def run(n, p, orders=(2, 4, 0)):
    g = primitive_root(p)
    # dlog table
    dlog = np.zeros(p, dtype=np.int64)
    v = 1
    for k in range(p-1):
        dlog[v] = k
        v = v*g % p
    mu = np.array([pow(g, (p-1)//n * k, p) for k in range(n)], dtype=np.int64)
    beta = np.log(p)/np.log(n)
    print(f"== n={n} p={p} beta={beta:.2f} ==  err-heur n^2/sqrt(p)={n*n/np.sqrt(p):.3f}")
    s0 = np.arange(p, dtype=np.int64)
    sh = (s0[:, None] - mu[None, :]) % p          # p x n shifts
    nz = sh != 0
    dl = dlog[sh]
    for order in orders:
        d = order if order else n
        j = (p-1)//d
        ph = np.exp(2j*np.pi * (j*dl % (p-1)) / (p-1)) * nz
        T = ph.sum(axis=1)
        A = np.abs(T)
        S2 = (A**2).sum(); S4 = (A**4).sum()
        wick2 = 2*p*n*n; wick3 = 3*p*n*n
        real = (d == 2)
        w = wick3 if real else wick2
        print(f"  order-{d} chi ({'real' if real else 'complex'}): S2={S2:.0f} (pred {n*p-n*n})"
              f"  S4/{'3' if real else '2'}pn^2 = {S4/w:.4f}   max|T|={A.max():.2f} sqrt(n)={np.sqrt(n):.2f} sqrt(n ln p)={np.sqrt(n*np.log(p)):.2f}")

run(8, 12289)
run(16, 65537)
run(16, 59393)
run(32, 786433)   # 786432 = 3*2^18, 32 | p-1
run(32, 12289)    # beta ~ 2.7 for contrast
