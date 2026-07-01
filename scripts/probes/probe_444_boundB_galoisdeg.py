"""
probe_444_boundB_galoisdeg.py -- the elimination degree AS A GALOIS/FIELD degree.

The genuine 'eliminant degree' is the number of distinct gamma-VALUES = (n/d)*O_P (the gamma's,
before the orbit fold), and O_P = #distinct J=gamma^{n/d}.  We measure both AND decompose them
through the cyclotomic structure to see where the C(n/2,.) vs C(n,.) split lives.

KEY measurement for Bound-B: the bad-gamma set is Galois-stable (S<->Galois conjugate subset gives
conjugate gamma), so #distinct gamma is a UNION OF GALOIS ORBITS. We compute, over F_p (char-0
model), how the gamma-set and J-set decompose, and crucially the ABSOLUTE elimination degree if we
do NOT use the squares structure (a generic point count) vs the descended one.

The decisive comparison the task wants:
  deg_gamma := #distinct gamma            (eliminant degree in gamma, pre-fold)
  O_P       := #distinct J = deg_gamma * d / n   (post dilation-orbit fold)
  and we check whether O_P tracks  C(n/2,r-1)  (descended) or  C(n,r-1)/(n/d) etc (un-descended).
We tabulate the RATIO O_P / C(n/2,r-1) and O_P*2^? to locate the residual exactly.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter

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

def full(n,r,e,f,p):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    gammas=set(); Js=set()
    M=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        gammas.add(g); Js.add(pow(g,nd,p))
    return len(gammas),len(Js),d,nd

LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
       5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}

if __name__=="__main__":
    p=PRIMES[0]
    print(f"# p={p}; deg_gamma = #distinct gamma (pre-fold eliminant degree); O_P=#J (post-fold)")
    print(f"{'r':>2}{'n':>4} {'line':>10} {'d':>3}{'n/d':>4} {'deg_gamma':>9} {'O_P':>5} "
          f"{'C(n/2,r-1)':>10} {'C(n,r-1)/(n/d)':>14} {'O_P/C(n/2,r-1)':>14}")
    for (r,n) in [(3,16),(3,32),(4,16),(4,32),(5,16),(6,16)]:
        e,f=LINES[r](n)
        dg,OP,d,nd=full(n,r,e,f,p)
        b_desc=comb(n//2,r-1)
        b_undesc=comb(n,r-1)/nd
        print(f"{r:>2}{n:>4} {('('+str(e)+','+str(f)+')'):>10} {d:>3}{nd:>4} {dg:>9} {OP:>5} "
              f"{b_desc:>10} {b_undesc:>14.1f} {OP/b_desc:>14.3f}")
