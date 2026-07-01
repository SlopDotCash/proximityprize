"""
probe_444_mech1_Jfactor.py -- does J=gamma^{n/d} FACTOR THROUGH mu_{n/2} data?

For SAME-PARITY lines, antipode g0=w^{n/2}=-1 FIXES gamma (proven exactly). The dilation orbit
of S under <w> has the antipode as an element of the gamma-stabilizer. We test several candidate
"mu_{n/2} descent" hypotheses for J:

 H1: J(S) depends only on the multiset S^2 = {s^2 : s in S} (which lives in mu_{n/2}).
     i.e. if S^2 = S'^2 as multisets then J(S)=J(S').   [the cleanest descent]
 H2: J(S) depends only on the (r-1)-subset structure: image of J has size <= C(n/2,r-1).
 H3: gamma itself is a function of power sums P_2,P_4,...,P_{2k} (even power sums only) of S.

We ALSO directly probe the candidate map  J <- (r-1)-subset of mu_{n/2}  by checking |image J|
vs C(n/2,r-1), and whether distinct-J classes biject to (r-1)-subsets of squares.

Same-parity maximizer line auto-detected.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import defaultdict

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
def gamma_of(Sidx,w,e,f,r,p):
    Spts=[pow(w,i,p) for i in Sidx]
    M=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return None
    H=hpow(Spts,M,p)
    her,her1,hfr,hfr1=H[e-r],H[e-r+1],H[f-r],H[f-r+1]
    if (her*hfr1-hfr*her1)%p: return None
    if hfr==0: return None
    g=(-her*pow(hfr,p-2,p))%p
    return None if g==0 else g

def maximizer(n,r,p):
    w=gen(n,p); a0=r+1
    subs=list(combinations(range(n),a0))
    Hc=[hpow([pow(w,i,p) for i in S],n,p) for S in subs]
    best=(0,None,0)
    for e in range(r,n):
        for f in range(r,n):
            if e==f or (e-f)%2!=0: continue
            if max(e-r+1,f-r+1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d; cos=set()
            for H in Hc:
                if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
                if H[f-r]==0: continue
                g=(-H[e-r]*pow(H[f-r],p-2,p))%p
                if g: cos.add(pow(g,nd,p))
            if len(cos)>best[0]: best=(len(cos),(e,f),d)
    return w,best

def run(n,r,p):
    w,(opmax,line,d)=maximizer(n,r,p)
    e,f=line; nd=n//d; half=n//2
    # collect (S^2-multiset-key, J, gamma) for all bad S
    J_by_sq=defaultdict(set)          # H1: key = sorted squared-index multiset -> set of J
    J_by_evenPS=defaultdict(set)      # H3': key = even power sums P_2..P_{2k} -> set of gamma
    allJ=set(); allgamma=set()
    k=r-1
    for Sidx in combinations(range(n),r+1):
        g=gamma_of(Sidx,w,e,f,r,p)
        if g is None: continue
        J=pow(g,nd,p); allJ.add(J); allgamma.add(g)
        sqkey=tuple(sorted((2*i)%n for i in Sidx))   # index of s^2 in mu_n is 2i mod n (in mu_{n/2})
        J_by_sq[sqkey].add(J)
        Spts=[pow(w,i,p) for i in Sidx]
        evenPS=tuple(sum(pow(z,2*j,p) for z in Spts)%p for j in range(1,k+1))
        J_by_evenPS[evenPS].add(g)
    H1=all(len(s)==1 for s in J_by_sq.values())
    H3=all(len(s)==1 for s in J_by_evenPS.values())
    bound=comb(half,k)
    print(f"r={r} n={n} same-parity max line=(x^{e},x^{f}) d={d} nd={nd}: O_P=|imJ|={len(allJ)}")
    print(f"    bound C(n/2,r-1)=C({half},{k})={bound}  O_P/bound={len(allJ)/bound:.3f}")
    print(f"    H1  J depends only on S^2 multiset: {H1}  (#distinct S^2 keys={len(J_by_sq)})")
    print(f"    H3  gamma depends only on even power sums P2..P2k: {H3}  (#keys={len(J_by_evenPS)})")
    # H1 refined: if H1 holds, how many distinct S^2 keys map to distinct J?
    if H1:
        sq2J={k_:next(iter(v)) for k_,v in J_by_sq.items()}
        print(f"    [H1 holds] #distinct S^2-keys producing distinct J = {len(set(sq2J.values()))}")

if __name__=="__main__":
    todo=[(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for p in PRIMES[:1]:
        for (r,n) in todo: run(n,r,p)
