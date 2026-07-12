#!/usr/bin/env python3
"""OC G224 definiteness test: is the PAR- per-mode integrand EXACTLY negative
(sign-definite quadratic form, clean theorem) or only near-negative (empirical)?

Key structural question. The parity halves satisfy a Newton recursion. Test the
hypothesis that the even/odd halves are NOT independent but tied by
    Or (odd half of R_r) is, mode-by-mode, a fixed multiple of Er, so the cross
    term Er*conj(Om)+Or*conj(Em) reduces to a real sign-definite kernel.

We compute per NON-TRIVIAL mode chi:
  k(chi) = conj(Wh) * (Erh*conj(Omh) + Orh*conj(Emh))   [the PAR- integrand *p^0]
and report:
  (i) is Re k(chi) <= 0 for EVERY chi (exact-ish, tol)?  count strict positives
      with |Re k| above a relative floor (real, not fp noise).
  (ii) the ratio Re k / |k| to see how close to termwise-real-negative it is.
Also test the alternative that Wh(chi) itself carries the sign: Re(Wh) sign census
on the support, since W = 2G - G translate count is real-symmetric-ish.
"""
import math
from collections import Counter
import numpy as np

def factor(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out
def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
    raise ValueError(p)
def subgroup(p,n):
    z=pow(primitive_root(p),(p-1)//n,p);grp=[];x=1
    for _ in range(n):grp.append(x);x=x*z%p
    return grp
def parts(n,hi=None):
    if n==0:yield ();return
    hi=n if hi is None or hi>n else hi
    for x in range(hi,0,-1):
        for tail in parts(n-x,x):yield (x,)+tail
def zlam(lam):
    return math.prod((j**m)*math.factorial(m) for j,m in Counter(lam).items())

def halves(p,grp,r,eta):
    even=np.zeros(p);odd=np.zeros(p)
    for lam in parts(r):
        c=((-1)**(sum(lam)-len(lam)))/zlam(lam)
        acc=np.zeros(p);acc[0]=1.0
        for part in lam:
            acc=np.fft.irfft(np.fft.rfft(acc)*np.fft.rfft(np.array(eta[part],dtype=float)),p)
        if (r-len(lam))%2==0: even+=c*acc
        else: odd+=c*acc
    return even,odd

def run(p,n,r):
    grp=subgroup(p,n)
    eta={j:[0]*p for j in range(1,r+1)}
    for j in range(1,r+1):
        for g in grp: eta[j][(j*g)%p]+=1
    W=np.zeros(p)
    for y in grp:
        for z in grp: W[(2*y-z)%p]+=1
    Er,Or_=halves(p,grp,r,eta);Em,Om=halves(p,grp,r-1,eta)
    Wh=np.fft.fft(W);Erh=np.fft.fft(Er);Orh=np.fft.fft(Or_)
    Emh=np.fft.fft(Em);Omh=np.fft.fft(Om)
    k=np.conj(Wh)*(Erh*np.conj(Omh)+Orh*np.conj(Emh))
    kk=k[1:]
    rek=kk.real
    scale=np.abs(kk)+1e-9
    # strict positives above relative floor 1e-6 of max|k|
    floor=1e-6*np.max(np.abs(rek))
    strict_pos=int(np.sum(rek>floor))
    strict_neg=int(np.sum(rek<-floor))
    near_zero=int(np.sum(np.abs(rek)<=floor))
    # is imaginary part negligible pairwise? (conj symmetry gives real sum)
    return strict_neg,strict_pos,near_zero,len(rek),float(np.max(np.abs(rek))),float(rek[rek>floor].sum() if strict_pos else 0.0),float(rek[rek<-floor].sum())

for (n,r,ps) in [(16,5,[97,257,1153]),(16,6,[97,257]),(32,5,[257,1153]),(32,6,[257]),(64,5,[257,1153])]:
    print(f"\n=== n={n} r={r} ===")
    for p in ps:
        if (p-1)%n:continue
        sn,sp,nz,tot,mx,pm,nm=run(p,n,r)
        print(f" p={p}: modes={tot} strict_neg={sn} strict_pos={sp} near0={nz} "
              f"| pos_mass={pm:.3e} neg_mass={nm:.3e} | max|Rek|={mx:.3e}")
