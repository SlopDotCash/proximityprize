#!/usr/bin/env python3
"""R18 PLATEAU lane probe.

Exact structure of S_2^D = sum_{s0 notin D} |I_H(s0)|^4, D = {0} u mu_n.

Tests:
 (1) EXACT: S_1^D = q*Sigma - |I(0)|^2 - Sigma^2/n          (depletion identity)
 (2) EXACT: spike = sum_{s0 in mu_n}|I|^4 = Sigma^4/n^3
 (3) 3-family decomposition: QuadSum = S_2/q; structured = 3 Sigma^2 - 3 quart;
     Off' = S_2/q - structured. Report q*Off' vs spike (dominance) and remainder.
 (4) PLATEAU: ratio = S_2^D/(3 q Sigma^2) = 1 - c/m?  c = (1-ratio)*m
 (5) DEPLETED-WICK: Wstar = 3 (S_1^D)^2/(q-1-n); ratio2 = S_2^D/Wstar; c2=(1-ratio2)*m
 (6) Sigma^2/n / (q*Sigma) = Sigma/(q n)  vs  1/m  (the 1/deg entry point)
"""
import numpy as np
from sympy import isprime

def find_prime(target, mod):
    # smallest prime >= target with p = 1 mod `mod`
    p = target + ((1 - target) % mod)
    while not isprime(p):
        p += mod
    return p

def subgroup(p, size, g):
    # subgroup of F_p^* of order `size`
    e = (p-1)//size
    h = pow(g, e, p)
    out = []
    x = 1
    for _ in range(size):
        out.append(x); x = x*x0 if False else (x*h) % p
    return sorted(set(out))

def primitive_root(p):
    from sympy import primitive_root as pr
    return pr(p)

rows = []
for n in (8, 16):
    for beta_lab, target in (("b3", n**3), ("b4", n**4)):
        for m in (2, 4, 8, 16):
            p = find_prime(target, n*m)
            q = p
            g = primitive_root(p)
            mun = subgroup(p, n, g)
            Hsize = (p-1)//m
            assert Hsize % n == 0
            H = subgroup(p, Hsize, g)
            # eta via FFT
            ind = np.zeros(p); ind[mun] = 1.0
            eta = np.fft.fft(ind)          # eta_fft[k] = sum_x e(-kx/p) = eta_{-k}
            # |eta_b|: symmetric under b->-b in abs; but we need eta_b itself:
            # eta_b = conj(eta_fft[b])  since eta_fft[b] = sum e(-bx/p)
            etab = np.conj(eta)            # etab[b] = eta_b
            f = np.zeros(p, dtype=complex)
            Harr = np.array(H)
            f[Harr] = np.conj(etab[Harr])
            # I(s0) = sum_b f[b] e(+2pi i b s0/p) = ifft(f)*p at s0
            I = np.fft.ifft(f) * p
            absI2 = np.abs(I)**2
            Sigma = float(np.sum(np.abs(etab[Harr])**2))
            quart = float(np.sum(np.abs(etab[Harr])**4))
            J0 = I[0]
            D = [0] + mun
            mask = np.ones(p, bool); mask[D] = False
            S1D = float(np.sum(absI2[mask]))
            S2 = float(np.sum(absI2**2))
            S2D = float(np.sum(absI2[mask]**2))
            spike = float(np.sum(absI2[mun]**2))
            # checks
            chk1 = S1D - (q*Sigma - abs(J0)**2 - Sigma**2/n)
            chk2 = spike - Sigma**4/n**3
            # diag values check I(s0 in mu_n) = Sigma/n
            chk3 = max(abs(I[s] - Sigma/n) for s in mun)
            structured = 3*Sigma**2 - 3*quart
            Offp = S2/q - structured
            wick = 3*q*Sigma**2
            ratio = S2D/wick
            c = (1-ratio)*m
            Wstar = 3*S1D**2/(q-1-n)
            ratio2 = S2D/Wstar
            c2 = (1-ratio2)*m
            dep = Sigma/(q*n)*m   # should be ~ (p-n)/p ~ 1
            rows.append((n, beta_lab, m, p, ratio, c, ratio2, c2,
                         chk1/max(S1D,1), chk2/max(spike,1), chk3,
                         q*Offp/spike if spike else 0, dep,
                         quart/Sigma**2*m, abs(J0)**2/(q*Sigma)))
            print(f"n={n:3d} {beta_lab} m={m:3d} p={p:9d} "
                  f"S2D/Wick={ratio:.4f} c={c:.3f} | S2D/W*={ratio2:.4f} c2={c2:+.3f} | "
                  f"chk1={chk1/max(S1D,1):.1e} chk2={chk2/max(spike,1):.1e} chk3={chk3:.1e} | "
                  f"qOff'/spike={q*Offp/spike:.4f} m*Sig/(qn)={dep:.4f} "
                  f"m*quart/S^2={quart/Sigma**2*m:.3f} |J0|^2/(qS)={abs(J0)**2/(q*Sigma):.2e}")
