#!/usr/bin/env python3
"""R19 DEPLETED task (b): thin-H trajectory of C(m) up to the extreme m=(p-1)/n (H=mu_n).

For fixed n and p, sweep m over ALL divisors of (p-1)/n; C(m) = S2D(q-1-n)/S1D^2.
Where does C cross 3? Compare against m ~ n^2/2. Also compute the H=mu_n endpoint
exactly and its 'EVT' prediction.
"""
import numpy as np
from sympy import isprime, primitive_root, divisors

def find_prime(target, mod):
    p = target + ((1 - target) % mod)
    while not isprime(p): p += mod
    return p

def run(n, beta):
    target = int(round(n**beta))
    p = find_prime(target, n)
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*h % p
    ind = np.zeros(p); ind[mun] = 1.0
    etab = np.conj(np.fft.fft(ind))
    mask = np.ones(p, bool); mask[[0]+mun] = False
    print(f"\nn={n} beta={beta} p={p} (p-1)/n={(p-1)//n}")
    ms = [d for d in divisors((p-1)//n)]
    ms = [m for m in ms if m <= (p-1)//n]
    # subsample if too many
    if len(ms) > 24:
        ms = sorted(set(ms[:8] + ms[::max(1,len(ms)//16)] + ms[-8:]))
    prev = None
    for m in sorted(ms):
        Hsize = (p-1)//m
        hH = pow(g, m, p)
        H = np.empty(Hsize, dtype=np.int64); x = 1
        for i in range(Hsize): H[i] = x; x = x*hH % p
        f = np.zeros(p, dtype=complex); f[H] = np.conj(etab[H])
        I = np.fft.ifft(f) * p
        absI2 = np.abs(I)**2
        S1D = float(np.sum(absI2[mask]))
        S2D = float(np.sum(absI2[mask]**2))
        C = S2D*(p-1-n)/S1D**2
        # kurtosis-style diagnostic: effective away-point count & max share
        mx = float(np.max(absI2[mask]))
        share = mx*mx/S2D
        print(f"  m={m:6d} (|H|={Hsize:7d}) C={C:.4f}  maxterm-share={share:.3f} "
              f"m/(n^2/2)={m/(n*n/2):.3f}")
        prev = C

for n, beta in ((8, 3.0), (8, 4.0), (16, 3.0), (16, 3.5), (16, 4.0), (32, 3.0)):
    run(n, beta)
