# Find the r=3 maximizer line & verify O_P=C(n/4,2). Print top lines by O_P,
# and also test the gamma def both ways (gamma=-he/hf vs the prompt's exact form).
from math import comb, gcd
from itertools import combinations
import sys
P1 = 2013265921
def mu_n(n,p):
    e=(p-1)//n
    for c in range(2,500):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return [pow(h,i,p) for i in range(n)]
def hser(elts,mmax,p):
    H=[0]*(mmax+1); H[0]=1
    for z in elts:
        for m in range(mmax,0,-1):
            H[m]=(H[m]+z*H[m-1])%p
    return H
def census(dom,n,p,r,e,f):
    a=r+1; ie,ie1,jf,jf1=e-r,e-r+1,f-r,f-r+1; mmax=max(ie,ie1,jf,jf1)
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
    nd=sum(1 for g in fiber if g!=0)
    return SonV,nd,gz,fiber
def run(n):
    p=P1; r=3; dom=mu_n(n,p)
    tOP=comb(n//4,2)
    rows=[]
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            if min(e-r,e-r+1,f-r,f-r+1)<0: continue
            SonV,nd,gz,fiber=census(dom,n,p,r,e,f)
            bad=nd+(1 if gz>0 else 0)
            d=gcd(abs(e-f),n); orbit=n//d; OP=nd//orbit if orbit else 0
            rows.append((OP,bad,SonV,e,f,d,orbit,nd))
    rows.sort(reverse=True)
    print(f"n={n}: target O_P=C(n/4,2)={tOP}, target #bad=n*C(n/4,2)+1={n*tOP+1}")
    print(f"  top 8 lines by O_P:")
    for OP,bad,SonV,e,f,d,orbit,nd in rows[:8]:
        print(f"    line(x^{e},x^{f}) O_P={OP} #bad={bad} S_on_V={SonV} d={d} orbit={orbit} nd={nd}")
    maxbad=max(r[1] for r in rows)
    print(f"  MAX #bad over all lines = {maxbad}; target #bad = {n*tOP+1}; match? {maxbad==n*tOP+1}")
if __name__=="__main__":
    for n in [int(x) for x in sys.argv[1:]] or [16]:
        run(n)
