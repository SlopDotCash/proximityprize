#!/usr/bin/env python3
"""R19 DEPLETED lane, task (a): dense scan of the depleted-Wick constant
C(n,m,beta) = S2D*(q-1-n)/(S1D)^2  (DepletedWickR2 constant; measured vs 3).

Prize-shaped region: beta in [3.5,4.4], m<=32, n>=16. Multiple primes per cell.
"""
import numpy as np, sys
from sympy import isprime, primitive_root

def primes_1mod(target, mod, k):
    p = target + ((1 - target) % mod)
    out = []
    while len(out) < k:
        if isprime(p): out.append(p)
        p += mod
    return out

def cell(p, n, m):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    mun = []
    x = 1
    for _ in range(n): mun.append(x); x = x*h % p
    hH = pow(g, m, p)
    Hsize = (p-1)//m
    H = np.empty(Hsize, dtype=np.int64)
    x = 1
    for i in range(Hsize): H[i] = x; x = x*hH % p
    ind = np.zeros(p); ind[mun] = 1.0
    etab = np.conj(np.fft.fft(ind))          # etab[b] = eta_b
    f = np.zeros(p, dtype=complex)
    f[H] = np.conj(etab[H])
    I = np.fft.ifft(f) * p
    absI2 = np.abs(I)**2
    Sigma = float(np.sum(np.abs(etab[H])**2))
    mask = np.ones(p, bool); mask[[0]+mun] = False
    S1D = float(np.sum(absI2[mask]))
    S2D = float(np.sum(absI2[mask]**2))
    C = S2D*(p-1-n)/S1D**2
    return C, Sigma

def main():
    results = {}
    sup_prize = (0, None)
    for n in (16, 32, 64):
        betas = (3.5, 3.8, 4.0, 4.2, 4.4) if n <= 32 else (3.5, 3.8, 4.0)
        for beta in betas:
            target = int(round(n**beta))
            if target > 3*10**7: continue
            for m in (2, 4, 8, 16, 32):
                nprimes = 3 if n < 64 else 2
                Cs = []
                for p in primes_1mod(target, n*m, nprimes):
                    C, Sig = cell(p, n, m)
                    Cs.append((C, p))
                cmax = max(Cs)[0]; cmin = min(Cs)[0]
                results[(n, beta, m)] = Cs
                print(f"n={n:3d} beta={beta:.1f} m={m:3d} "
                      f"C=[{cmin:.4f},{cmax:.4f}] " +
                      " ".join(f"{c:.4f}@{p}" for c, p in Cs), flush=True)
                if n >= 16 and m <= 32 and 3.5 <= beta <= 4.4:
                    for c, p in Cs:
                        if c > sup_prize[0]: sup_prize = (c, (n, beta, m, p))
    print("\nSUP over prize-shaped region:", sup_prize)
    # n-trend at beta=4, m=8: fit C = Cinf + a/n
    print("\nn-trend (beta=4.0, per m): mean C per n")
    for m in (2, 4, 8, 16, 32):
        xs = []
        for n in (16, 32, 64):
            key = (n, 4.0, m)
            if key in results:
                xs.append((n, np.mean([c for c, _ in results[key]])))
        print(f" m={m:3d}: " + " ".join(f"n={n}:{c:.4f}" for n, c in xs))

main()
