#!/usr/bin/env python3
"""R15 B2 probe (FFT version): S_r = sum_{s0}|I_H(s0)|^{2r}, Wick check, worst-case vs sqrt|H|*M.
I_H(s0) = sum_b w_b e_p(b s0), w_b = conj(eta_b)*1_H(b)  => I = conj(FFT(conj(w)))-style; use direct
convention: np.fft.ifft(w)*p gives sum_b w_b e^{+2 pi i b s0/p}. eta = ifft(1_mun)*p likewise.
"""
import numpy as np, math, random

def dfact(k):
    out = 1
    while k > 1: out *= k; k -= 2
    return out

def factor(x):
    fs, d = set(), 2
    while d*d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in factor(p-1)):
            return g

def analyze(p, n, deg, rmax=6, seed=1, randctl=True):
    g = prim_root(p)
    m = (p-1)//n
    mun = np.zeros(p)
    x = 1
    gm = pow(g, m, p)
    for _ in range(n):
        x = x*gm % p if _ else pow(g, 0, p)  # start at 1
    # build mu_n properly
    mun_set = set()
    x = 1
    for _ in range(n):
        mun_set.add(x); x = x*gm % p
    ind = np.zeros(p, dtype=complex)
    for x in mun_set: ind[x] = 1
    eta = np.fft.ifft(ind)*p   # eta[b] = sum_{x in mun} e^{2pi i bx/p}
    gd = pow(g, deg, p)
    H_set = set(); x = 1
    for _ in range((p-1)//deg):
        H_set.add(x); x = x*gd % p
    Hidx = np.array(sorted(H_set))
    w = np.zeros(p, dtype=complex)
    w[Hidx] = np.conj(eta[Hidx])
    I = np.fft.ifft(w)*p       # I[s0] = sum_b w_b e^{2pi i b s0 /p}
    absI = np.abs(I)
    Sig = float(np.sum(np.abs(eta[Hidx])**2))
    M = float(np.max(np.abs(eta[1:])))
    worst = float(np.max(absI))
    out = dict(p=p, n=n, deg=deg, H=len(Hidx), M=M, worst=worst,
               ratio_B=worst/(math.sqrt(len(Hidx))*M), rows=[])
    # random-phase control
    if randctl:
        rng = np.random.default_rng(seed)
        wr = np.zeros(p, dtype=complex)
        wr[Hidx] = np.abs(eta[Hidx])*np.exp(2j*np.pi*rng.random(len(Hidx)))
        Ir = np.abs(np.fft.ifft(wr)*p)
    for r in range(1, rmax+1):
        Sr = float(np.sum(absI**(2*r)))
        wick = p * dfact(2*r-1) * Sig**r
        rr = float(np.sum(Ir**(2*r)))/wick if randctl else float('nan')
        out['rows'].append((r, Sr/wick, rr))
    return out

def cases():
    cs = []
    for n in (8, 16):
        for deg in (2, 4):
            L = n*deg//math.gcd(n, deg)
            got, p = 0, 100
            while got < 3:
                p += 1
                if p % L == 1 and all(p % d for d in range(2, int(p**0.5)+1)) and ((p-1)//deg) % n == 0:
                    cs.append((p, n, deg)); got += 1
    for n, deg in ((8,2),(8,4),(16,2),(16,4),(32,2)):
        p = n**4
        while True:
            p += 1
            L = n*deg//math.gcd(n,deg)
            if p % L == 1 and all(p % d for d in range(2, int(p**0.5)+1)) and ((p-1)//deg) % n == 0:
                cs.append((p, n, deg)); break
    return cs

if __name__ == "__main__":
    for (p, n, deg) in cases():
        res = analyze(p, n, deg)
        print(f"p={res['p']} n={res['n']} deg={res['deg']} |H|={res['H']} M={res['M']:.3f} "
              f"worst|I|={res['worst']:.1f} worst/(sqrt|H|*M)={res['ratio_B']:.3f}", flush=True)
        for r, rt, rr in res['rows']:
            flag = "OK " if rt <= 1 else "FAIL"
            print(f"   r={r}: S_r/Wick={rt:.4g} [{flag}]  randphase/Wick={rr:.4g}", flush=True)
