#!/usr/bin/env python3
"""R17: the deg=2 EXACT bridge and the Weil-conditional r=2 rung.

Claims:
 (E1) EXACT: I_QR(s0) = (q*1_G(s0) - n + g(chi)*W(s0))/2, where
      W(s0) = sum_{y in mu_n} chi(s0-y), g = Gauss sum, chi = Legendre.
      (H = QR = index-2 subgroup; mu_n <= QR requires 2 | (p-1)/n.)
 (E2) fourth moment of W over ALL s: S_W = sum_s W(s)^4 = 3n^2 p * (1+o(1)) + Weil error;
      check S_W vs 3n^2 p and vs 3n^2 p + 3 n^4 sqrt(p).
 (E3) hence S2'(deg2)/Wick2 -> 1/4 as beta grows; check the exact constant.
 (E4) the away-rung r=2 at deg 2 from the pieces: verify numerically the final inequality
      with explicit constants for several beta>4 cells.
"""
import numpy as np, math
from sympy import isprime

def factor(x):
    fs,d=set(),2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in factor(p-1)): return g

def run(p,n):
    g=prim_root(p); gm=pow(g,(p-1)//n,p); mun=[]; x=1
    for _ in range(n): mun.append(x); x=x*gm%p
    ind=np.zeros(p,dtype=complex)
    for x in mun: ind[x]=1
    eta=np.fft.ifft(ind)*p
    # chi via index parity
    chi=np.zeros(p)
    x=1
    for k in range(p-1):
        chi[x]=1 if k%2==0 else -1
        x=x*g%p
    # H=QR
    H=np.where(chi==1)[0]
    Hs=set(H.tolist())
    if not set(mun)<=Hs:
        print(f"p={p} n={n}: SKIP mu_n not in QR"); return
    w=np.zeros(p,dtype=complex); w[H]=np.conj(eta[H])
    I=np.fft.ifft(w)*p
    # W(s) via FFT: W = ifft( fft(chi_as_func) ... ) do directly: W(s)=sum_y chi(s-y)
    # conv: W = (chi * ind_rev)(s): W(s) = sum_y chi(s-y)*ind(y) -> cyclic convolution chi (*) ind
    W=np.real(np.fft.ifft(np.fft.fft(chi)*np.fft.fft(ind.real)))
    # gauss sum g(chi) = sum_b chi(b) e(b/p) with SAME psi convention as eta: psi(x)=e^{+2pi i x/p}
    psi=np.exp(2j*np.pi*np.arange(p)/p)
    gs=np.sum(chi*psi)
    # E1
    onG=np.zeros(p); onG[mun]=1
    pred=(p*onG - n + gs*W)/2
    e1=np.max(np.abs(I-pred))
    # E2
    SW=float(np.sum(W**4))
    main=3*n*n*p
    weil=3*n**4*math.sqrt(p)
    # E4: away rung deg2
    mask=np.ones(p,bool); mask[0]=False; mask[mun]=False
    absI=np.abs(I)
    S2p=float(np.sum(absI[mask]**4))
    Sig=float(np.sum(np.abs(eta[H])**2))
    wick=3*p*Sig**2
    print(f"p={p:>9} n={n:>3} beta={math.log(p)/math.log(n):.2f} E1(max err)={e1:.2e} "
          f"SW/main={SW/main:.4f} SW/(main+weil)={SW/(main+weil):.4f} S2'/Wick={S2p/wick:.4f}")

def primes_1mod(m,count,start):
    out=[]; x=max(start-start%m+1,m+1)
    while len(out)<count and x<9_000_000:
        if isprime(x): out.append(x)
        x+=m
    return out

for n in (8,16,32):
    for scale in (n**3, n**4, min(n**5,6_000_000)):
        for p in primes_1mod(2*n,2,scale):
            run(p,n)
