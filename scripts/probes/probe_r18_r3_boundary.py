#!/usr/bin/env python3
"""R18 opener: the r=3 rung at deg=2 in the Weil gap beta in (4,6).

After r17: r=2 at deg=2 is Weil-classical for beta>4. The r=3 rung needs the SIXTH moment of
W; the sextic Weil error n^6*sqrt(q) beats the pairing main term 15n^3*q only when beta>6.
The prize sits at beta ~ 5.3: r=3 there is the FIRST genuinely-open rung at deg=2.

Calibrate: S3' / Wick3 and the raw sixth moment of W vs its pairing main term
(15 n^3 q vs measured), for beta = 3..6, to see how much cancellation beyond Weil is
actually present (i.e. whether the truth has room or is knife-edge in the gap).
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
    chi=np.zeros(p); x=1
    for k in range(p-1):
        chi[x]=1 if k%2==0 else -1
        x=x*g%p
    H=np.where(chi==1)[0]
    if not set(mun)<=set(H.tolist()): return
    w=np.zeros(p,dtype=complex); w[H]=np.conj(eta[H])
    I=np.fft.ifft(w)*p; absI=np.abs(I)
    Sig=float(np.sum(np.abs(eta[H])**2))
    W=np.real(np.fft.ifft(np.fft.fft(chi)*np.fft.fft(ind.real)))
    mask=np.ones(p,bool); mask[0]=False; mask[mun]=False
    S3p=float(np.sum(absI[mask]**6))
    wick3=15*p*Sig**3
    SW6=float(np.sum(W**6))
    main6=15*n**3*p
    weil6=5*n**6*math.sqrt(p)
    print(f"p={p:>9} n={n:>3} beta={math.log(p)/math.log(n):.2f} S3'/W3={S3p/wick3:.4f} "
          f"SW6/main6={SW6/main6:.4f} weil6/main6={weil6/main6:.2f} "
          f"SW6/(main6+weil6)={SW6/(main6+weil6):.4f}")

def primes_1mod(m,count,start):
    out=[]; x=max(start-start%m+1,m+1)
    while len(out)<count and x<9_000_000:
        if isprime(x): out.append(x)
        x+=m
    return out

for n in (8,16):
    for beta in (3.0,4.0,4.5,5.0,5.3,6.0):
        for p in primes_1mod(2*n,1,int(n**beta)):
            run(p,n)
for p in primes_1mod(64,1,32**4):
    run(p,32)
