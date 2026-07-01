"""
DECISIVE r=3 check: does J = gamma^{n/d} factor through the pair (s1,s2) = (a+b, c+d)
in the P=1 normalization?  The BoundA 'proof' counts #(s1+s2)^2 and claims it = O_P.
For that count to be an UPPER BOUND on true O_P, J must be a FUNCTION of (s1+s2) (or of (s1,s2)).
MECHANISM-2 says J carries finer info. We test directly on the TRUE bad set:
  group all bad S by their (s1,s2) [normalized], and check whether J is constant within each group,
  and whether #distinct J equals #distinct(s1+s2)^2.
"""
from math import comb, gcd
from itertools import combinations
from collections import defaultdict
PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def inv(a,p): return pow(a,p-2,p)
def h_powers(elts,M,p):
    P=[0]*(M+1)
    for i in range(1,M+1): P[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+P[i]*H[m-i])%p
        H[m]=(s*inv(m,p))%p
    return H

def analyze(n,p,r=3):
    w=gen(n,p)
    e,f=n//2,n//2-1
    d=gcd((e-f)%n,n)
    M=max(e-r,f-r,e-r+1,f-r+1)
    # for each bad S, record (dilation-invariant of (s1,s2)) -> J.
    # dilation-invariant version of s1+s2: e1 scales as g, so (s1+s2)^?/... ; use the proven W=e1^2/P.
    # We use the FULL normalized invariant the BoundA proof uses: I3 = e1^4/e4 (dilation-inv).
    # Claim under test: J is a function of I3 (then #J <= #I3 <= #(s1+s2)^2 via 2-to-1).
    byI3=defaultdict(set)
    Js=set()
    for Sidx in combinations(range(n),r+1):
        Spts=[pow(w,i,p) for i in Sidx]
        H=h_powers(Spts,M,p)
        her,her1=H[e-r],H[e-r+1]; hfr,hfr1=H[f-r],H[f-r+1]
        if (her*hfr1-hfr*her1)%p!=0: continue
        if hfr==0: continue
        g=(-her*inv(hfr,p))%p
        if g==0: continue
        # elementary symmetric e1,e4 of the 4-subset
        vals=Spts
        e1=sum(vals)%p
        e4=(vals[0]*vals[1]%p*vals[2]%p*vals[3])%p
        if e4==0:
            I3=None
        else:
            I3=(pow(e1,4,p)*inv(e4,p))%p
        J=pow(g,n//d,p)
        Js.add(J)
        byI3[I3].add(J)
    multi=sum(1 for k,v in byI3.items() if len(v)>1)
    Jconst = all(len(v)==1 for v in byI3.values())
    return len(Js), len(byI3), Jconst, multi

if __name__=="__main__":
    p=PRIMES[0]
    for n in [16,32,64]:
        nJ,nI3,const,multi=analyze(n,p)
        print(f"n={n}: #distinct J={nJ}  #distinct I3={nI3}  J-constant-per-I3={const}  (#I3 with >1 J={multi})  #J==#I3? {nJ==nI3}")
