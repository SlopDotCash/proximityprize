"""
probe_444_boundB_resdeg.py -- compute the ACTUAL gamma-eliminant degree from the structured r=3
resultant, descended (squares) vs un-descended (full mu_n), to report the CONSTANT the elimination
delivers and whether it equals C(n/2,r-1) or only Theta(n^{r-1}) with a worse constant.

We build, over F_p, the eliminant in gamma as follows. Fix the orbit gauge q=ab=1 (so the dilation
is quotiented). The bad gammas at q=1 are roots of a univariate poly E_desc(gamma) whose degree we
read by counting distinct gamma at q=1 (=the fiber). We compare:
  desc  : restrict a,b to SQUARES (mu_{n/2}), c,d to NONSQUARES  -> #distinct gamma at q=1
  undesc: allow a,b,c,d any of mu_n with ab=-cd                  -> #distinct gamma at q=1
The ratio (undesc/desc) should be ~2^r (the sharpness factor). And we check desc-degree vs
C(n/4,2)/C(n/2,2)/C(n,2).
"""
from math import comb, gcd
from itertools import combinations

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def gamma_of(S,e,f,p=P):
    H=hpow(S,max(e-3+1,f-3+1),p)
    if (H[e-3]*H[f-3+1]-H[f-3]*H[e-3+1])%p: return None
    if H[f-3]==0: return None
    g=(-H[e-3]*pow(H[f-3],p-2,p))%p
    return g if g else None

def fiber_at_q1(n,e,f,descended,p=P):
    """Count distinct gamma over 4-subsets {a,b,c,d} of mu_n with ab=-cd and ab=1 (q=1 gauge).
       descended=True restricts a,b squares, c,d nonsquares (the proven r=3 structure)."""
    w=gen(n,p)
    elts=[pow(w,i,p) for i in range(n)]
    gammas=set()
    if descended:
        A=[2*i for i in range(n//2)]; Cset=[2*i+1 for i in range(n//2)]
    else:
        A=list(range(n)); Cset=list(range(n))
    for (ia,ib) in combinations(A,2):
        a,b=elts[ia],elts[ib]
        if (a*b)%p!=1: continue   # q=1
        for (ic,idd) in combinations(Cset,2):
            c,d=elts[ic],elts[idd]
            if (c*d)%p!=(-1)%p: continue   # cd=-q=-1
            g=gamma_of([a,b,c,d],e,f,p)
            if g: gammas.add(g)
    return len(gammas)

if __name__=="__main__":
    print("r=3 q=1 fiber gamma-degree: descended (squares) vs un-descended (full mu_n):")
    print(f"{'n':>4} {'desc':>5} {'undesc':>7} {'undesc/desc':>11} {'C(n/4,2)':>9} {'C(n/2,2)':>9} {'C(n,2)':>8}")
    for n in [16,32]:
        e,f=n//2,n//2-1
        dd=fiber_at_q1(n,e,f,True)
        uu=fiber_at_q1(n,e,f,False)
        ratio=uu/dd if dd else 0
        print(f"{n:>4} {dd:>5} {uu:>7} {ratio:>11.2f} {comb(n//4,2):>9} {comb(n//2,2):>9} {comb(n,2):>8}")
