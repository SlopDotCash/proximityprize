# Independent cross-check of the BILINEAR reduction at r=5 (and r=4) against the
# prompt's stated TRUE-maximizer O_P values:
#   r=4 (x^{n/2+2},x^{n/4+1}): O_P=9,97,(897)
#   r=5 (x^{n/2+1},x^{n-1}):   O_P=11,90
#   r=6:                       O_P=14,185  (line not given; skip)
from math import comb, gcd
from itertools import combinations
import sys
P1=2013265921; P2=3221225473
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def hser(elts,mmax,p):
    # H(t)=prod_z 1/(1-z t) mod t^{mmax+1}; FORWARD loop (verified vs brute h_m).
    H=[0]*(mmax+1); H[0]=1
    for z in elts:
        for m in range(1,mmax+1):
            H[m]=(H[m]+z*H[m-1])%p
    return H
def census(n,p,r,e,f):
    a=r+1; ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1
    assert min(ie,ie1,jf,jf1)>=0,(ie,ie1,jf,jf1)
    mmax=max(ie,ie1,jf,jf1); dom=mu_n(n,p)
    fiber={}; gz=0; SonV=0
    for S in combinations(range(n),a):
        elts=[dom[i] for i in S]; H=hser(elts,mmax,p)
        he,he1,hf,hf1=H[ie],H[ie1],H[jf],H[jf1]
        if (he*hf1-hf*he1)%p==0:
            SonV+=1
            if hf%p!=0:
                g=(-he*pow(hf,p-2,p))%p
                if g==0: gz+=1
                fiber[g]=fiber.get(g,0)+1
    nz=sum(1 for g in fiber if g!=0)
    d=gcd(abs(e-f),n); orbit=n//d; OP=nz//orbit if orbit else 0
    return SonV,nz,gz,OP,orbit,fiber
def run(r,line_fn,expected,ns):
    for n in ns:
        e,f=line_fn(n)
        SonV,nz,gz,OP,orbit,fiber=census(n,P1,r,e,f)
        exp = expected.get(n,'?')
        print(f"r={r} n={n} line(x^{e},x^{f}): O_P={OP} expected={exp} match={OP==exp}  "
              f"S_on_V={SonV} nz_gamma={nz} orbit={orbit}")
if __name__=="__main__":
    print("=== r=4 (x^{n/2+2},x^{n/4+1}) expect O_P 9,97 ===")
    run(4, lambda n:(n//2+2,n//4+1), {16:9,32:97}, [16,32])
    print("=== r=5 (x^{n/2+1},x^{n-1}) expect O_P 11,90 ===")
    run(5, lambda n:(n//2+1,n-1), {16:11,32:90}, [16,32])
