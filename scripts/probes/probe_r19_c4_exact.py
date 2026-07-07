#!/usr/bin/env python3
"""Exact total quadruple mass Sum_{quads} |M| and its scaling in m.

Reports: A2 = Sum|M| / (|X|^2 n^2 q), A3 = Sum|M| / (|X|^3 n^2 q),
paired part, off part, and S4A/(p^2 |X|^2 n^2 q) (the true Wick-level).
"""
import numpy as np, itertools
from sympy import isprime, primitive_root

def find_prime(target, mod):
    p = target + ((1 - target) % mod)
    while not isprime(p): p += mod
    return p

def run(n, beta, m):
    target = int(round(n**beta))
    p = find_prime(target, n*m)
    g = primitive_root(p)
    dlog = np.zeros(p, dtype=np.int64); x = 1
    for k in range(p-1): dlog[x] = k; x = x*g % p
    h = pow(g, (p-1)//n, p)
    mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*h % p
    om = np.exp(2j*np.pi/m)
    ind = np.zeros(p); ind[mun] = 1.0
    Find = np.fft.fft(ind)
    Ts = []
    for j in range(1, m):
        arr = om**((j*dlog) % m); arr[0] = 0.0
        Ts.append(np.fft.ifft(np.fft.fft(np.conj(arr))*Find))
    mm = m-1
    Ts = np.array(Ts)
    # Pmat rows = pair products Ts[a]*Ts[b], Gram = Pmat conj(Pmat)^T gives all M
    pairs = list(itertools.product(range(mm), repeat=2))
    Pmat = np.empty((mm*mm, p), dtype=np.complex128)
    for i, (a, b) in enumerate(pairs):
        Pmat[i] = Ts[a]*Ts[b]
    Gram = Pmat @ np.conj(Pmat.T)
    vals = np.abs(Gram)
    tot = float(vals.sum())
    paired = 0.0
    for i, (a, b) in enumerate(pairs):
        for j, (c, d) in enumerate(pairs):
            if sorted((c, d)) == sorted((a, b)):
                paired += float(vals[i, j])
    offt = tot - paired
    del Pmat, Gram
    q = p
    base2 = mm*mm*n*n*q; base3 = mm**3*n*n*q
    print(f"n={n} beta={beta} m={m} p={p}: tot/b2={tot/base2:.3f} tot/b3={tot/base3:.3f} "
          f"paired/b2={paired/base2:.3f} off/b2={offt/base2:.3f} off/b3={offt/base3:.3f}",
          flush=True)

for (n, beta, m) in ((16, 3.5, 4), (16, 3.5, 8), (16, 3.5, 16),
                     (16, 4.0, 4), (16, 4.0, 8), (16, 4.0, 16),
                     (16, 4.2, 8), (16, 4.2, 16),
                     (32, 3.5, 8), (32, 4.0, 4), (32, 4.0, 8),
                     (16, 4.0, 32)):
    run(n, beta, m)
