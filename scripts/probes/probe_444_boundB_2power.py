"""
probe_444_boundB_2power.py -- verify the 2^r (sharpness) factor that the antipodal descent must
supply, for general r, by comparing the bad-gamma count restricted to the SQUARES-structured
subsets vs the full mu_n, at the maximizer line. This quantifies exactly how much the descent buys
and whether it suffices to land at C(n/2,r-1).

For each (r,n,maximizer line): O_P (full) is known. We compute the 'descended degree' = the
gamma-eliminant degree you get if you ONLY count subsets respecting the antipodal/parity structure
that the descent imposes, and compare its constant to C(n/2,r-1).

Concretely the cleanest invariant: compare
   bezout_undesc = C(n,   r-1)     (naive, columns of full Vandermonde; the WEAK bound)
   bezout_desc   = C(n/2, r-1)     (descended; the TARGET)
and the achieved O_P, reporting O_P/bezout_desc and bezout_undesc/bezout_desc (= the 2^{r-1}
factor the descent must and does supply).
"""
from math import comb, gcd
from itertools import combinations

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H
def OP_of(n,r,e,f,p):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    Js=set(); M=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: Js.add(pow(g,nd,p))
    return len(Js),d

LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
       5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}

if __name__=="__main__":
    p=PRIMES[0]
    print("descent budget: O_P vs descended C(n/2,r-1) vs un-descended C(n,r-1):")
    print(f"{'r':>2}{'n':>4} {'O_P':>5} {'C(n/2,r-1)':>10} {'C(n,r-1)':>9} "
          f"{'undesc/desc':>11} {'2^(r-1)':>8} {'O_P/desc':>9}")
    for (r,n) in [(3,16),(3,32),(4,16),(4,32),(5,16),(6,16)]:
        e,f=LINES[r](n)
        OP,d=OP_of(n,r,e,f,p)
        bd=comb(n//2,r-1); bu=comb(n,r-1)
        print(f"{r:>2}{n:>4} {OP:>5} {bd:>10} {bu:>9} {bu/bd:>11.2f} {2**(r-1):>8} {OP/bd:>9.3f}")
