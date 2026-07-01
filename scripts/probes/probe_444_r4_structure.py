# Structural analysis of variety V at r=4 (n=16, exhaustive), to assess V's "degree"
# as a constraint and the crude chain #bad <= #{S on V} <= K viability.
#  - compare S_on_V to codim-1 heuristic C(n,r+1)/n and to K
#  - characterize the large-fiber special orbit (which gammas? which S?)
#  - check whether S_on_V is well below K with slack growing (the crude chain hope)
from math import comb, gcd
from itertools import combinations
from collections import Counter
import sys
P1=2013265921; P2=3221225473
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def hser(elts,mmax,p):
    H=[0]*(mmax+1); H[0]=1
    for z in elts:
        for m in range(1,mmax+1):
            H[m]=(H[m]+z*H[m-1])%p
    return H
def full(n,p,r,e,f):
    a=r+1; ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1; mmax=max(ie,ie1,jf,jf1)
    dom=mu_n(n,p)
    SonV=0; fiber={}; gz=0; inf_ct=0
    # also track, per bad S: is hf==0 (the "inf" pins) and the gamma; and how many S have he==0
    he_zero_count=0
    for S in combinations(range(n),a):
        elts=[dom[i] for i in S]; H=hser(elts,mmax,p)
        he,he1,hf,hf1=H[ie],H[ie1],H[jf],H[jf1]
        if (he*hf1-hf*he1)%p==0:
            SonV+=1
            if he%p==0: he_zero_count+=1
            if hf%p==0: inf_ct+=1
            else:
                g=(-he*pow(hf,p-2,p))%p
                if g==0: gz+=1
                fiber[g]=fiber.get(g,0)+1
    return SonV,fiber,gz,inf_ct,he_zero_count
def analyze(n):
    p=P1; r=4; e=n//2+2; f=n//4+1; a=r+1
    SonV,fiber,gz,inf_ct,hez=full(n,p,r,e,f)
    Cnr=comb(n,a)
    K=(1<<r)*comb(n//2,r)
    nz=sum(1 for g in fiber if g!=0)
    d=gcd(abs(e-f),n); orbit=n//d
    szc=Counter(c for g,c in fiber.items())
    print(f"=== n={n} r=4 line(x^{e},x^{f}) ===")
    print(f" total (r+1)-subsets C(n,{a})={Cnr}")
    print(f" S_on_V={SonV}   codim-1 heuristic C(n,a)/n={Cnr/n:.1f}   ratio S_on_V/(C/n)={SonV/(Cnr/n):.3f}")
    print(f" K=2^r*C(n/2,r)={K}   S_on_V/K={SonV/K:.4f}   K/S_on_V={K/SonV:.3f}")
    print(f" nz_gamma={nz}  zero_present={1 if gz>0 else 0}  inf_pins(hf=0)={inf_ct}  he_zero_on_V={hez}")
    print(f" #bad=nz+[zero]={nz+(1 if gz>0 else 0)}   bad/K={(nz+(1 if gz>0 else 0))/K:.4f}")
    print(f" orbit n/d={orbit}  O_P=nz/orbit={nz//orbit}")
    print(f" fiber-size dist (size->#gamma): {dict(sorted(szc.items()))}")
    # the special large-fiber orbit
    big=sorted(((c,g) for g,c in fiber.items() if g!=0),reverse=True)[:orbit+2]
    bigsizes=sorted(set(c for g,c in fiber.items() if g!=0))
    print(f" distinct fiber sizes among nonzero gammas: {bigsizes}")
    # sum check: sum of fiber sizes = SonV - inf_ct (pins with hf=0 not in fiber)
    print(f" sum(fiber sizes)={sum(fiber.values())}  + inf_pins {inf_ct} = {sum(fiber.values())+inf_ct} (=S_on_V {SonV}? {sum(fiber.values())+inf_ct==SonV})")
for n in [int(x) for x in sys.argv[1:]] or [16,32]:
    analyze(n)
