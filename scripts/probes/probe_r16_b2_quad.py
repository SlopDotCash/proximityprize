#!/usr/bin/env python3
"""R16 B2: exact quadruple decomposition of the r=2 rung of the s0-moment tower.

S_2 = sum_{s0} |I_H(s0)|^4 = q * Q,   Q = sum_{b1+b2=b3+b4, bi in H} cE(b1)cE(b2)E(b3)E(b4),
E(b) = eta_b (mu_n-coset invariant), cE = conj.

Classes (eta is constant on mu_n-cosets, mu_n <= H):
  Q_pair   : {b3,b4} = {b1,b2} as multisets  ->  2*Sig^2 - sum|eta|^4  (exact, positive)
  Q_struct : b3 = u*b1, b4 = v*b2 (u,v in mu_n) or crossed b3=u*b2,b4=v*b1, minus overlap with
             pairing. Weights are |eta_b1|^2 |eta_b2|^2 (positive!).
  Q_rest   : everything else (genuinely off-structure; hoped Wick/Sig^2 scale).

Questions:
  (Q1) identity check: S_2 == q*Q (FFT two ways).
  (Q2) is q*Q_struct ~ diagMass (= sum_{s0 in D} |I|^4, D = {0} u mu_n)? exact relation?
  (Q3) is q*(Q - Q_pair - Q_struct) <= Wick-ish (3 q Sig^2 - 2 q Sig^2 = q Sig^2)?
  (Q4) hence: does S'_2 <= 3 q Sig^2 reduce to positive-structured bookkeeping?

2026-07-07 verdict: Q1 is stable and S'_2/Wick2 stays < 1 in the tested cells, but the naive
Q3 shortcut is false by large factors.  The r=2 away-Wick target therefore needs a cancellation
identity/estimate for the full raw fourth moment after exact diagonal deletion, not the simple
``pair + structured + bounded rest'' bookkeeping attempted here.
"""
import numpy as np, math, itertools

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

def run(p, n, deg):
    g = prim_root(p); m = (p-1)//n
    gm = pow(g, m, p); mun = []; x = 1
    for _ in range(n): mun.append(x); x = x*gm % p
    munset = set(mun)
    ind = np.zeros(p, dtype=complex)
    for x in mun: ind[x] = 1
    eta = np.fft.ifft(ind)*p          # eta[b] = sum_{y in mun} e(-2pi i b y / p)? sign convention consistent
    gd = pow(g, deg, p); Hs = set(); x = 1
    for _ in range((p-1)//deg): Hs.add(x); x = x*gd % p
    H = np.array(sorted(Hs))
    if not (munset <= Hs):
        print(f"p={p} n={n} deg={deg}: SKIP (mu_n is not contained in H)")
        return
    w = np.zeros(p, dtype=complex); w[H] = np.conj(eta[H])
    I = np.fft.ifft(w)*p; absI = np.abs(I)
    Sig = float(np.sum(np.abs(eta[H])**2))
    S2 = float(np.sum(absI**4))
    # Q via convolution: f(b) = conj(eta_b) 1_H(b); (f conv f)(x) = sum_{b1+b2=x} f(b1)f(b2)
    F = np.fft.fft(w)
    conv = np.fft.ifft(F*F)           # length-p cyclic convolution = additive conv mod p
    Q = float(np.sum(np.abs(conv)**2))
    id_err = abs(S2 - p*Q)/S2
    # diagonal mass
    D = [0] + mun
    diagMass = float(np.sum(absI[D]**4))
    S2away = S2 - diagMass
    wick2 = 3.0 * p * Sig**2
    # Q_pair exact
    quart = float(np.sum(np.abs(eta[H])**4))
    Q_pair = 2*Sig**2 - quart
    # Q_struct exact via closed form:
    # class A: b3=u b1, b4=v b2, u,v in mun; constraint b1(1-u) = b2(v-1).
    #   u=1: forces v=1 or b2=0 -> u=1,v=1 is the identity pairing (in Q_pair). skip u=1 or v=1.
    #   u,v != 1: b2 = b1 (1-u) * inv(v-1); contributes |eta_b1|^2 |eta_b2|^2 if b2 in H.
    # class B (crossed): b3=u b2, b4=v b1: b1+b2 = u b2 + v b1 -> b1(1-v) = b2(u-1);
    #   u=v=1 impossible unless...  1-v=0 & u-1=0 -> identity again (the swap pairing).
    #   u,v !=1: b2 = b1(1-v)*inv(u-1).
    # Overlap A∩B and overlap with pairing must be removed; we compute the union count with
    # multiplicity as quadruple-set, so instead: enumerate structured quadruples as SET of
    # (b1,b2,b3,b4) tuples for small |H|; for large |H| use closed form and accept multiplicity
    # bookkeeping (report both).
    abs2 = np.zeros(p); abs2[H] = np.abs(eta[H])**2
    Q_structA = 0.0
    for u in mun:
        if u == 1: continue
        for v in mun:
            if v == 1: continue
            fac = (1-u) * pow(v-1, p-2, p) % p
            # b2 = b1 * fac ; need b1,b2 in H; since H multiplicative subgroup, b2 in H iff fac in H (b1 in H)
            if fac % p in Hs and fac % p != 0:
                # sum over b1 in H of |eta_b1|^2 |eta_{b1*fac}|^2
                idx2 = (H * fac) % p
                Q_structA += float(np.sum(abs2[H] * abs2[idx2]))
    # crossed class has identical value by symmetry of the parametrization (b1<->b2 relabel)
    Q_struct = 2*Q_structA
    Q_rest = Q - Q_pair - Q_struct
    print(f"p={p} n={n} deg={deg} |H|={len(H)} Sig={Sig:.4g}")
    print(f"  (Q1) identity |S2 - qQ|/S2 = {id_err:.2e}")
    print(f"  S2={S2:.4g} diagMass={diagMass:.4g} S2'={S2away:.4g} Wick2={wick2:.4g} S2'/Wick2={S2away/wick2:.4g}")
    print(f"  qQ_pair={p*Q_pair:.4g} qQ_struct={p*Q_struct:.4g} qQ_rest={p*Q_rest:.4g}")
    print(f"  (Q2) qQ_struct/diagMass = {p*Q_struct/diagMass:.4g}")
    print(f"  (Q3) qQ_rest/(q Sig^2) = {Q_rest/Sig**2:.4g}   [need <= 1 for the reduction]")
    print(f"  (Q4) [S2' - 2qSig^2 - qQ_struct + diagMass]/ (q Sig^2) = {(S2away - 2*p*Sig**2 - p*Q_struct + diagMass)/(p*Sig**2):.4g}")

for (p, n, deg) in [(193,8,2),(241,8,2),(353,8,4),(449,16,4),(4129,8,2),(4129,8,4),
                    (65537,16,2),(65537,16,4),(1048897,32,2),(1048897,32,4)]:
    run(p, n, deg)
