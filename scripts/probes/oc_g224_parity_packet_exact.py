#!/usr/bin/env python3
"""OC G224 (fast, exact-integer via FFT with integer rounding + z-clearing).
Determines whether the Newton PAR- parity packet is sign-forced (theorem) or a
finite-size coincidence. Exact-integer: coeffs cleared by global lcm L_r; all
convolutions via numpy FFT then np.rint (exact since values are bounded ints).
Cross-checked: PAR+ + PAR- == A (exact int) on every cell."""
import math
from collections import Counter
from fractions import Fraction
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
    assert x==1 and len(set(grp))==n
    return grp
def parts(n,hi=None):
    if n==0:yield ();return
    hi=n if hi is None or hi>n else hi
    for x in range(hi,0,-1):
        for tail in parts(n-x,x):yield (x,)+tail
def zlam(lam):
    return math.prod((j**m)*math.factorial(m) for j,m in Counter(lam).items())

def cconv_int(a,b,p):
    fa=np.fft.rfft(a);fb=np.fft.rfft(b)
    return np.rint(np.fft.irfft(fa*fb,p)).astype(object)

def halfsums(p,grp,r,eta,L):
    even=np.zeros(p,dtype=object);odd=np.zeros(p,dtype=object)
    for lam in parts(r):
        z=zlam(lam);sign=(-1)**(sum(lam)-len(lam))
        cnum=L//z*sign  # integer L-scaled coeff
        acc=np.zeros(p,dtype=object);acc[0]=1
        for part in lam:
            acc=cconv_int(acc.astype(np.float64),np.array(eta[part],dtype=np.float64),p)
        parity=(r-len(lam))%2
        if parity==0: even=even+cnum*acc
        else: odd=odd+cnum*acc
    return even,odd

def run(p,n,r):
    grp=subgroup(p,n)
    eta={j:[0]*p for j in range(1,r+1)}
    for j in range(1,r+1):
        for g in grp: eta[j][(j*g)%p]+=1
    W=[0]*p
    for y in grp:
        for z in grp: W[(2*y-z)%p]+=1
    W=np.array(W,dtype=object)
    Lr=math.lcm(*[zlam(lam) for lam in parts(r)])
    Lm=math.lcm(*[zlam(lam) for lam in parts(r-1)])
    er_e,er_o=halfsums(p,grp,r,eta,Lr)
    em_e,em_o=halfsums(p,grp,r-1,eta,Lm)
    # verify integer R_r = (er_e+er_o)/Lr
    Rr=(er_e+er_o); Rm=(em_e+em_o)
    assert all(int(x)%Lr==0 for x in Rr)
    assert all(int(x)%Lm==0 for x in Rm)
    def corr_scaled(Ra,Rb):
        # sum_s Ra(s)*(W conv Rb-reflected)(s); returns exact int (L-scaled by Lr*Lm)
        # Wc(s)=sum_t W(t) Rb(s-t) = (W conv Rb)(s)
        Wc=cconv_int(W.astype(np.float64),np.array([int(x) for x in Rb],dtype=np.float64),p)
        return sum(int(Ra[s])*int(Wc[s]) for s in range(p))
    ee=corr_scaled(er_e,em_e);eo=corr_scaled(er_e,em_o)
    oe=corr_scaled(er_o,em_e);oo=corr_scaled(er_o,em_o)
    sEe=sum(int(x) for x in er_e);sEo=sum(int(x) for x in er_o)
    sMe=sum(int(x) for x in em_e);sMo=sum(int(x) for x in em_o)
    def dc(sa,sb): return n*n*sa*sb
    PARp=p*(ee+oo)-(dc(sEe,sMe)+dc(sEo,sMo))
    PARm=p*(eo+oe)-(dc(sEe,sMo)+dc(sEo,sMe))
    mass=math.comb(n,r)*math.comb(n,r-1)
    # exact A (L-scaled): p*sum W*Corr(Rr,Rm) - n^2 mass, all *Lr*Lm
    Corr=cconv_int(W.astype(np.float64),np.array([int(x) for x in Rm],dtype=np.float64),p)
    A=p*sum(int(Rr[s])*int(Corr[s]) for s in range(p)) - n*n*mass*Lr*Lm
    assert PARp+PARm==A,(p,n,r)
    return A,PARp,PARm

CELLS=[(8,[41,73,97,113,193,257,449]),
       (16,[97,113,193,257,353,433,577,641,881,1153]),
       (32,[97,193,257,449,577,1153,1217,1409,2113,3617]),
       (64,[193,257,449,577,641,769,1153,1409,2113])]
for r in (5,6):
    print(f"\n############ r={r} ############")
    for n,ps in CELLS:
        if n<=r:continue
        allneg=True;anyA=set();rows=0
        line=[]
        for p in ps:
            if (p-1)%n:continue
            A,PARp,PARm=run(p,n,r)
            sA='+' if A>0 else '-';anyA.add(sA)
            if PARm>=0:allneg=False
            rows+=1
            line.append(f"p{p}:A{sA}/PAR-{'+' if PARm>0 else '-'}({float(abs(PARm)/max(1,abs(A))):.1f}x)")
        print(f"  n={n} r={r}: "+"  ".join(line))
        print(f"     => PAR- ALWAYS NEG this row: {allneg}; A signs: {sorted(anyA)}; cells:{rows}")
