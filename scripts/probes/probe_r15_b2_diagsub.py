#!/usr/bin/env python3
"""R15 B2 follow-up: diagonal structure of the s0-tower.
Claims to test:
 (D1) For s0 in mu_n: I_H(s0) = Sig/n exactly (Sig = sum_{b in H}|eta_b|^2).
 (D2) More generally for s0 in H: I_H(s0) = sum_t conj(eta_t) eta_{t s0} = coset autocorrelation;
      spikes only at s0 in mu_n?
 (D3) Diagonal-subtracted tower S'_r = sum_{s0 not in mu_n} |I|^{2r}: does Wick hold to r=6?
 (D4) off-diagonal worst vs sqrt(|H|)*M (the real Problem B scale).
"""
import numpy as np, math

def dfact(k):
    o=1
    while k>1: o*=k; k-=2
    return o
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

def run(p,n,deg,rmax=6):
    g=prim_root(p); m=(p-1)//n
    gm=pow(g,m,p); mun=[]; x=1
    for _ in range(n): mun.append(x); x=x*gm%p
    ind=np.zeros(p,dtype=complex)
    for x in mun: ind[x]=1
    eta=np.fft.ifft(ind)*p
    gd=pow(g,deg,p); Hs=set(); x=1
    for _ in range((p-1)//deg): Hs.add(x); x=x*gd%p
    Hidx=np.array(sorted(Hs))
    w=np.zeros(p,dtype=complex); w[Hidx]=np.conj(eta[Hidx])
    I=np.fft.ifft(w)*p; absI=np.abs(I)
    Sig=float(np.sum(np.abs(eta[Hidx])**2))
    M=float(np.max(np.abs(eta[1:])))
    # D1
    d1=[abs(I[s]-Sig/n) for s in mun]
    print(f"p={p} n={n} deg={deg} |H|={len(Hidx)} Sig/n={Sig/n:.2f} M={M:.3f} sqrt|H|M={math.sqrt(len(Hidx))*M:.1f}")
    print(f"  D1 max|I(s0)-Sig/n| over s0 in mu_n: {max(d1):.2e}")
    mask=np.ones(p,bool)
    mask[0]=False
    mask[mun]=False
    offworst=float(np.max(absI[mask]))
    print(f"  D4 off-diag worst |I|={offworst:.1f}  ratio vs sqrt|H|M = {offworst/(math.sqrt(len(Hidx))*M):.3f}")
    # top 8 offsets
    top=np.argsort(absI)[-8:][::-1]
    print("  top |I| offsets:", [(int(s), round(float(absI[s]),1), s in Hs, int(s) in mun) for s in top])
    for r in range(1,rmax+1):
        Sp=float(np.sum(absI[mask]**(2*r)))
        wick=p*dfact(2*r-1)*Sig**r
        print(f"   r={r}: S'_r/Wick={Sp/wick:.4g} [{'OK' if Sp/wick<=1 else 'FAIL'}]")

for (p,n,deg) in [(193,8,2),(241,8,2),(353,8,4),(449,16,4),(4129,8,2),(4129,8,4),(65537,16,2),(65537,16,4),(1048897,32,2)]:
    run(p,n,deg)
