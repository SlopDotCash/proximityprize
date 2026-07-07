"""
probe_444_boundA_general.py -- generalize the r=3 mechanism (scale-invariant symmetric coords)
to r>=4. Confirm J=gamma^{n/d} is a function of the scale-invariant ratios of e_k(S), find which
combination, and measure the count vs C(n/2,r-1).

Setup: S=(r+1)-subset of mu_n. e_1..e_{r+1} elementary symmetric. Scale-invariant coords:
  among e_k (deg k), the ratios e_k^{(r+1)}/e_{r+1}^{k} (deg 0) and similar. There are r genuinely
  independent scale-invariant coords (since dim of config of r+1 pts mod dilation = r).
J=gamma^{n/d} is dilation-invariant => a function of these r coords.

We TEST: (a) J const per (e_1..e_{r+1}) of course; (b) J const per the scale-invariant vector
  V = ( e_k^{r+1} / e_{r+1}^k )_{k=1..r}  ; (c) whether some SINGLE ratio determines J (like I3
  did at r=3); (d) the COUNT of distinct J = O_P vs C(n/2,r-1).
We use the maximizer lines and a couple others.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,4000):
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
def esym(elts,p):
    E=[1]
    for z in elts:
        newE=E+[0]
        for i in range(len(E),0,-1):
            newE[i]=(newE[i]+E[i-1]*z)%p
        E=newE
    return E
def inv(a,p): return pow(a,p-2,p)

def study(n,r,e,f,p):
    a0=r+1; w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    M=max(e-r+1,f-r+1)
    rows=[]
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        E=esym(xs,p)  # E[1..r+1]
        # scale-invariant vector V_k = e_k^{r+1}/e_{r+1}^k
        er1=E[r+1]
        V=tuple((pow(E[k],r+1,p)*inv(pow(er1,k,p),p))%p for k in range(1,r+1))
        rows.append((J,V,E))
    OP=len(set(x[0] for x in rows))
    # is J const per V?
    J2V=defaultdict(set); V2J=defaultdict(set)
    for J,V,E in rows: J2V[J].add(V); V2J[V].add(J)
    const=all(len(s)==1 for s in J2V.values())
    inj=all(len(s)==1 for s in V2J.values())
    # which single coordinate V_k (or a simple combo) is injective with J?
    single=[]
    for k in range(r):
        J2vk=defaultdict(set); vk2J=defaultdict(set)
        for J,V,E in rows:
            J2vk[J].add(V[k]); vk2J[V[k]].add(J)
        c=all(len(s)==1 for s in J2vk.values()); ij=all(len(s)==1 for s in vk2J.values())
        single.append((k+1,c,ij,len(vk2J)))
    return dict(OP=OP,const=const,inj=inj,nV=len(V2J),single=single,Cnh=comb(n//2,r-1))

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),
           5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32),(4,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    p=PRIMES[0]
    print(f"# p={p}  -- is J a function of scale-invariant V=(e_k^{{r+1}}/e_{{r+1}}^k)?")
    for (r,n) in todo:
        e,f=LINES[r](n)
        R=study(n,r,e,f,p)
        print(f"r={r} n={n} O_P={R['OP']} C(n/2,r-1)={R['Cnh']}: J const-per-V={R['const']} V-inj={R['inj']} #V={R['nV']}")
        print(f"    per-coord (k,const,inj,#vals): {R['single']}")
