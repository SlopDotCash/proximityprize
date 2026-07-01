"""
probe_444_angleC_squares.py -- pin down the SQUARES-SUBGROUP (mu_{n/2}) mechanism behind the
load-bearing 'n/2' in O_P <= C(n/2, r-1).

In the prize regime the bound MUST be ~C(n/2,r-1), not C(n,r-1) (which fails K by 2^7). So the
proof must use the index-2 squares subgroup mu_{n/2}=<w^2>.  We test structural claims:

 (S1) gamma^{n/d} depends only on the image of S under squaring x->x^2 (i.e. on the multiset
      {x_i^2} in mu_{n/2})?  -> then O_P <= #images <= C(n/2 + r, r+1)-ish via mu_{n/2}.
 (S2) The bad gammas gamma^{n/d} are all SQUARES in F_p (lie in a fixed index-2 coset)? or
      n/d-th powers landing in a structured set of size ~C(n/2,r-1)?
 (S3) Map each bad gamma-orbit to a SUBSET of the n/2 antipodal pairs {x,-x}: e.g. the set of
      pairs P such that |S cap P| is odd (or =1). Is this map INJECTIVE on gamma-orbits, with
      image in (r-1)-subsets? -> O_P <= C(n/2, r-1) directly.
 (S4) parity of |S cap (each antipodal pair)|: count pairs hit oddly; is it constant = r-1?
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
    w=gen(n,p); a0=r+1; mult=pow(w,(e-f)%n,p); d=gcd((e-f)%n,n); nd=n//d
    g2S=defaultdict(list)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,max(e-r+1,f-r+1),p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if g: g2S[g].append(Sidx)
    nz=set(g2S)
    # coset invariant J = gamma^{n/d}
    Jvals=set(pow(g,nd,p) for g in nz); OP=len(Jvals)
    # (S2): are all J squares mod p? legendre
    def legendre(a): return pow(a,(p-1)//2,p)
    leg=Counter(legendre(J) for J in Jvals)
    # (S3/S4): for each bad S, count antipodal pairs hit oddly. antipodal: i and i+n/2.
    half=n//2
    oddpairs_dist=Counter()
    # map J -> set of 'odd-hit pair-index sets'
    J2pairsets=defaultdict(set)
    for g,Ss in g2S.items():
        J=pow(g,nd,p)
        for S in Ss:
            cnt=Counter(i%half for i in S)
            oddpairs=frozenset(k for k,v in cnt.items() if v%2==1)
            oddpairs_dist[len(oddpairs)]+=1
            J2pairsets[J].add(oddpairs)
    # is the odd-hit-pairset CONSTANT per J? (=> good invariant)
    const_per_J = all(len(v)==1 for v in J2pairsets.values())
    # if constant, are they distinct across J & of size r-1?
    if const_per_J:
        reps=[next(iter(v)) for v in J2pairsets.values()]
        sizes=Counter(len(x) for x in reps)
        distinct=len(set(reps))
        print(f"    (S3) odd-hit-pairset CONSTANT per J: True; #distinct={distinct} (==O_P? {distinct==OP}); size-dist={dict(sizes)}")
    else:
        nbad=sum(1 for v in J2pairsets.values() if len(v)>1)
        print(f"    (S3) odd-hit-pairset constant per J: False ({nbad}/{OP} J's have >1 pairset)")
    print(f"    (S2) Legendre(J) dist (1=square,p-1=nonsquare): {dict(leg)}")
    print(f"    (S4) #odd-hit antipodal pairs over bad S: {dict(sorted(oddpairs_dist.items()))}")
    return OP

if __name__=="__main__":
    LINES={3:lambda n:(n//2,n//2-1),4:lambda n:(n//2+2,n//4+1),5:lambda n:(n//2+1,n-1),6:lambda n:(n//2+4,n//2+2)}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    print("squares-subgroup / antipodal-folding mechanism:")
    for (r,n) in todo:
        e,f=LINES[r](n)
        print(f"  r={r} n={n} (x^{e},x^{f}):")
        study(n,r,e,f)
