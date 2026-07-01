"""
Independent ground-truth: r=3, line (n/2, n/2-1). Brute-force the TRUE bad set on V,
compute true O_P = #distinct J (J = gamma^{n/d}), and compare to C(n/4,2).
Also: independently compute the bad-set structure and check the {2 squares, 2 nonsquares, ab=-cd}
claim, and whether O_P = C(n/4,2) EXACTLY (both primes) and persists to n=128,256.
"""
from math import comb, gcd
from itertools import combinations
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

def true_OP(n,p,r=3):
    w=gen(n,p)
    e,f=n//2,n//2-1
    d=gcd((e-f)%n,n)
    M=max(e-r,f-r,e-r+1,f-r+1)
    Js=set(); zero=False; nbad=0
    for Sidx in combinations(range(n),r+1):
        Spts=[pow(w,i,p) for i in Sidx]
        H=h_powers(Spts,M,p)
        her,her1=H[e-r],H[e-r+1]; hfr,hfr1=H[f-r],H[f-r+1]
        if (her*hfr1-hfr*her1)%p!=0: continue
        nbad+=1
        if hfr==0: continue
        g=(-her*inv(hfr,p))%p
        if g==0: zero=True; continue
        J=pow(g,n//d,p)
        Js.add(J)
    return len(Js), d, zero, nbad

if __name__=="__main__":
    for p in PRIMES:
        print(f"# prime {p}")
        for n in [16,32,64]:
            OP,d,z,nb=true_OP(n,p)
            print(f"  n={n}: TRUE O_P={OP}  C(n/4,2)={comb(n//4,2)}  match={OP==comb(n//4,2)}  d={d} zero?={z} #bad={nb} (n/d)*O_P={(n//d)*OP}")
