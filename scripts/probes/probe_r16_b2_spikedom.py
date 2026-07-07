#!/usr/bin/env python3
"""R16 B2: wide stress test of the SPIKE-DOMINANCE candidate at r=2 (and the r=3 analogue).

Important current verdict:
  * The original narrow r=2 away-Wick sweep (n <= 32, deg in {2,4}) looked safely true.
  * This wider stress test finds secondary-spike failures for D={0} union mu_n, e.g.
    n=64, deg=8, p=7681 has S2'/Wick ~= 1.0048 and S2'/(2qSigma^2) ~= 1.5072.
  * Therefore the old universal r=2 target needs a refined diagonal set or a restricted regime.

Candidates (D = {0} u mu_n, T = off-pairing quadruple mass, quart = sum_{b in H}|eta_b|^4):
  (C1) exactness: I(s0) = Sig/n for all s0 in mu_n            [expected EXACT, mu_n <= H]
  (C2) qT <= diagMass + q*quart   <=>   S2' <= 2 q Sig^2      [the sharp r=2 candidate]
  (C3) S2' <= 3 q Sig^2 (the Wick rung as stated in Lean)
  (C4) r=3 pairing-only analogue: S3' <= 6 q Sig^3 (vs Wick's 15)
  (C5) I(0) = n * eta_H(1) when -1 in H                        [expected EXACT]

Sweep: n in {8,16,32,64}, deg in {2,4,8}, several primes p = 1 mod n*deg (so mu_n <= H),
including beta ~ 2..4 sizes where feasible for FFT (p <= ~2e6).
"""
import numpy as np, math
from sympy import isprime

def factor(x):
    fs, d = set(), 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in factor(p-1)): return g

def primes_1mod(m, count, start):
    out, x = [], max(start - start % m + 1, m + 1)
    while len(out) < count:
        if x > 2_200_000: break
        if isprime(x): out.append(x)
        x += m
    return out

def run(p, n, deg):
    g = prim_root(p); m = (p-1)//n
    gm = pow(g, m, p); mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*gm % p
    ind = np.zeros(p, dtype=complex)
    for x in mun: ind[x] = 1
    eta = np.fft.ifft(ind)*p
    gd = pow(g, deg, p); Hsize = (p-1)//deg
    Hs = set(); x = 1
    for _ in range(Hsize): Hs.add(x); x = x*gd % p
    if not set(mun) <= Hs:
        return None
    H = np.array(sorted(Hs))
    w = np.zeros(p, dtype=complex); w[H] = np.conj(eta[H])
    I = np.fft.ifft(w)*p; absI = np.abs(I)
    Sig = float(np.sum(np.abs(eta[H])**2))
    quart = float(np.sum(np.abs(eta[H])**4))
    D = [0] + mun
    mask = np.ones(p, bool); mask[D] = False
    # C1 exactness
    c1 = max(abs(I[s] - Sig/n) for s in mun)
    # C5
    etaH1 = np.sum(np.exp(-2j*np.pi*H/p))  # eta_H(1) with ifft*p convention: matches eta def
    c5 = abs(I[0] - n*etaH1) if (p-1) % (2*deg) == 0 else float('nan')  # -1 in H iff deg | (p-1)/2
    S2p = float(np.sum(absI[mask]**4))
    S3p = float(np.sum(absI[mask]**6))
    r2sharp = S2p / (2*p*Sig**2)
    r2wick  = S2p / (3*p*Sig**2)
    r3pair  = S3p / (6*p*Sig**3)
    r3wick  = S3p / (15*p*Sig**3)
    ok = "OK " if r2sharp <= 1 and r3pair <= 1 else "FAIL"
    print(f"{ok} p={p:>8} n={n:>3} deg={deg:>2} |H|={Hsize:>7} beta={math.log(p)/math.log(n):.2f} "
          f"C1={c1:.1e} C5={c5:.1e} S2'/2qS^2={r2sharp:.4f} S2'/Wick={r2wick:.4f} "
          f"S3'/6qS^3={r3pair:.4f} S3'/Wick3={r3wick:.4f}")
    return r2sharp, r3pair

worst2 = worst3 = 0.0
for n in (8, 16, 32, 64):
    for deg in (2, 4, 8):
        got = 0
        for scale in (n**2, n**3, 200*n**2, n**4):
            if got >= 4: break
            for p in primes_1mod(n*deg, 2, scale):
                if p < n*deg + 2 or p > 2_200_000: continue
                r = run(p, n, deg)
                if r:
                    worst2 = max(worst2, r[0]); worst3 = max(worst3, r[1]); got += 1
print(f"WORST: S2'/(2qSig^2) = {worst2:.4f}   S3'/(6qSig^3) = {worst3:.4f}")
