#!/usr/bin/env python3
"""R16 R2RUNG probe: r=2 rung of diagonal-subtracted incidence tower.
S_2^D = sum_{s0 not in D} |I_H(s0)|^4  vs Wick = p*3*Sigma^2, D={0} u mu_n.
Measures every candidate unconditional chain's two sides.
"""
import numpy as np
from sympy import isprime

def order(g, p):
    o, x = 1, g
    while x != 1:
        x = x * g % p; o += 1
    return o

def primitive_root(p):
    for g in range(2, p):
        if order(g, p) == p - 1:
            return g

def run(n, deg, p):
    assert isprime(p) and (p - 1) % (n * deg) == 0 and (p - 1) // deg % n == 0
    g = primitive_root(p)
    # mu_n
    gn = pow(g, (p - 1) // n, p)
    mun = set()
    x = 1
    for _ in range(n):
        mun.add(x); x = x * gn % p
    # H = index-deg subgroup
    gH = pow(g, deg, p)
    H = set()
    x = 1
    for _ in range((p - 1) // deg):
        H.add(x); x = x * gH % p
    assert mun <= H
    # eta_b via FFT: eta_b = sum_{x in mun} e(bx/p)
    ind = np.zeros(p)
    for x in mun: ind[x] = 1.0
    # eta[b] = sum_x ind[x] e^{2pi i bx/p} = conj(fft)(b)
    eta = np.conj(np.fft.fft(ind))  # fft gives sum ind[x] e^{-2pi i bx/p}
    Hmask = np.zeros(p, bool)
    for b in H: Hmask[b] = True
    gvec = np.zeros(p, complex)
    gvec[Hmask] = np.conj(eta[Hmask])
    # I(s0) = sum_b gvec[b] e^{2pi i b s0 /p}
    I = np.conj(np.fft.fft(gvec))
    Sigma = float(np.sum(np.abs(eta[Hmask])**2))
    M = float(np.max(np.abs(eta[1:])))
    absI4 = np.abs(I)**4
    absI2 = np.abs(I)**2
    D = mun | {0}
    Dmask = np.zeros(p, bool)
    for s in D: Dmask[s] = True
    S2 = float(np.sum(absI4))
    spike = float(np.sum(absI4[Dmask]))
    S2D = S2 - spike
    wick = p * 3.0 * Sigma**2
    supAway2 = float(np.max(absI2[~Dmask]))
    # second moment away
    S1D = float(np.sum(absI2[~Dmask]))
    # diagonal quadruples (b-space): 2 Sigma^2 - sum |eta|^4 over H
    sum4 = float(np.sum(np.abs(eta[Hmask])**4))
    Diag = 2 * Sigma**2 - sum4
    Off = S2 / p - Diag
    # unweighted E(H): E = (1/p) sum_t |hat1_H(t)|^4
    hatH = np.conj(np.fft.fft(Hmask.astype(float)))
    EH = float(np.sum(np.abs(hatH)**4) / p)
    Hc = len(H)
    print(f"n={n} deg={deg} p={p} |H|={Hc}")
    print(f"  Sigma={Sigma:.4g}  M={M:.4g}  M^2/n={M*M/n:.3f}")
    print(f"  RUNG: S2D/wick = {S2D/wick:.4f}   (S2D={S2D:.4g}, wick={wick:.4g})")
    print(f"  CHAIN1 Holder: supAway^2/(3 Sigma) = {supAway2/(3*Sigma):.3f}"
          f"   supAway^2*S1D / wick = {supAway2*S1D/wick:.3f}")
    print(f"  CHAIN1b n^2 p bound: n^2*p*S1D / wick = {n*n*p*S1D/wick:.3f}")
    print(f"  CHAIN2 quad-split: p*Diag/wick={p*Diag/wick:.3f}  p*Off/wick={p*Off/wick:.3f}"
          f"  (p*Off - spike)/wick = {(p*Off-spike)/wick:.3f}")
    print(f"  CHAIN3 M4E: p*M^4*E(H)/wick = {p*M**4*EH/wick:.3f}"
          f"   E(H)/(|H|^4/p) = {EH/(Hc**4/p):.3f}")
    print(f"  spike/wick = {spike/wick:.3f}  S1D/(p*Sigma) = {S1D/(p*Sigma):.4f}")

cases = []
# find primes: p = 1 mod n*deg with n | (p-1)/deg
for (n, deg) in [(8,2),(8,4),(16,2),(16,4),(32,2)]:
    found = 0
    p = n * deg + 1
    picks = []
    while found < 3 and p < 300000:
        p += n * deg
        if isprime(p) and (p - 1) // deg % n == 0:
            # take small, mid, ~n^4-ish
            picks.append(p)
            found += 1 if len(picks) in (1,) else 0
            if len(picks) >= 60: break
    # choose spread
    ps = []
    all_p = []
    p = n * deg + 1
    while p < max(4 * n**4, 5000):
        p += n * deg
        if isprime(p) and (p - 1) // deg % n == 0:
            all_p.append(p)
    if all_p:
        ps = [all_p[0], all_p[len(all_p)//2], all_p[-1]]
    for p in dict.fromkeys(ps):
        run(n, deg, p)
