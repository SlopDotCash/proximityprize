"""
probe_444_angleC_orbitrep.py -- look for the COMBINATORIAL ORIGIN of O_P <= C(n/2, r-1).

Idea: O_P = #distinct gamma-orbits. Each orbit's bad-S can be dilation-normalized (S -> S + t mod n)
to a canonical rep. Try to find an INJECTION from bad gamma-orbits into a set of size C(n/2, r-1),
e.g. (r-1)-subsets of a fixed n/2-element index set, after pinning structural constraints.

Concretely test several injection hypotheses:
  (HI-1) bad orbit <-> the GAP MULTISET of S (cyclic differences) determines gamma-orbit, and gap
         multisets of (r+1)-subsets of Z/n number ... ?
  (HI-2) bad gamma-orbit determined by S's image in Z/(n/2) (fold by antipodal map i->i+n/2)?
  (HI-3) the bad-S, normalized to contain 0 AND with the dilation+? quotient, has r-1 free even/odd
         positions.

We MEASURE: for the maximizer line, list normalized orbit-reps of bad S (one S per gamma-orbit),
and inspect: how many DISTINCT (a) gap-multisets, (b) folded-index-sets, (c) sorted index tuples
mod the antipodal involution. Compare each count to O_P and to C(n/2,r-1).
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

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

def study(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; mult=pow(w,(e-f)%n,p); d=gcd((e-f)%n,n)
    g2S=defaultdict(list)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: g2S[g].append(Sidx)
    nz=set(g2S)
    # orbit reps under gamma-dilation
    rem=set(nz); orbits=[]
    while rem:
        x=next(iter(rem)); o=set(); cur=x
        for _ in range(n): o.add(cur); cur=cur*mult%p
        orb=o&nz; orbits.append(orb); rem-=o
    OP=len(orbits)
    # For each gamma-orbit, gather all S over all gammas in the orbit; compute invariants
    gapsets=set(); foldsets=set(); sortedmod=set()
    for orb in orbits:
        # collect one canonical S-invariant per orbit. Use the union of S over the orbit, but we
        # want a single descriptor. Take, over all S mapping to any gamma in orb, the set of
        # gap-multisets / folded index sets, and check they're constant per orbit (=> good invariant).
        these=[]
        for g in orb: these.extend(g2S[g])
        gm=set(); fl=set(); sm=set()
        for S in these:
            Ss=sorted(S)
            gaps=tuple(sorted((Ss[(i+1)%a0]-Ss[i])%n for i in range(a0)))
            gm.add(gaps)
            fl.add(tuple(sorted(set(i%(n//2) for i in S))))
            sm.add(tuple(sorted(min(i,(i+n//2)%n) for i in S)))
        # add ONE representative invariant per orbit (the min) to global set
        gapsets.add(min(gm)); foldsets.add(min(fl)); sortedmod.add(min(sm))
    print(f"  r={r} n={n} (x^{e},x^{f}) d={d}: O_P={OP} C(n/2,r-1)={comb(n//2,r-1)}")
    print(f"    #distinct gap-multiset reps = {len(gapsets)}  (== O_P? {len(gapsets)==OP})")
    print(f"    #distinct folded-index reps  = {len(foldsets)} (== O_P? {len(foldsets)==OP})")
    print(f"    #distinct antipodal-min reps = {len(sortedmod)} (== O_P? {len(sortedmod)==OP})")

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    print("orbit-rep combinatorial invariants:")
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
