"""
probe_444_mech2_diffset.py -- the SURVIVING candidate: the dilation-invariant pairwise-DIFFERENCE
SET of S (translation-invariant), folded onto mu_{n/2}, as a bounded-to-one map J -> subset.

For r=3 the within-part diff pair {|a-b|,|c-d|} was constant-per-J (a genuine invariant), image size
n/4-ish, and bounded 2-to-1.  Generalize: per J take ANY bad S, form the multiset of pairwise index
diffs D(S)={ (i-j) mod n }, fold to mu_{n/2} by |.| (min(x,n-x)). Test:
   (i)  is D(S) (or its square-fold) CONSTANT across the J-orbit? (dilation-invariant: yes, since
        diffs are translation-invariant; the question is constancy across DIFFERENT bad S w/ same J)
   (ii) #distinct images vs O_P (injectivity / fiber bound)
   (iii) is #image <= C(n/2,r-1)?  AND is max-fiber*#image-or rather is O_P itself <= C(n/2,r-1)
        (which we know) -- the POINT is whether THIS map furnishes the bound.

We measure the image as a subset of {0,..,n/2} (folded diffs) and its size; we want the image to be
expressible as an (r-1)-subset (or at most r-1 'free' diffs).  Also test the SQUARE-CLASS difference
set: diffs of the squared roots (2i mod n) folded.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,2000):
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
def collect(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list); Mmax=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return w,{},d,nd
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J2S[pow(g,nd,p)].append(Sidx)
    return w,J2S,d,nd

def study(n,r,e,f):
    w,J2S,d,nd=collect(n,r,e,f)
    OP=len(J2S); tgt=comb(n//2,r-1)
    print(f"\n  r={r} n={n} (x^{e},x^{f}) par({e%2},{f%2}): O_P={OP} C(n/2,r-1)={tgt}")
    if OP==0: return
    half=n//2
    def fold(x): return min(x%n,(-x)%n)
    maps={
      'fulldiffset': lambda S:frozenset(fold(i-j) for i in S for j in S if i!=j),
      'sqdiffset': lambda S:frozenset(fold(2*(i-j)) for i in S for j in S if i!=j),
      'sorted-gap-vector': lambda S:tuple(sorted((S[k+1]-S[k])%n for k in range(len(S)-1))),
    }
    for name,fn in maps.items():
        J2img=defaultdict(set)
        for J,Ss in J2S.items():
            for S in Ss:
                Ss2=sorted(S)
                J2img[J].add(fn(Ss2))
        const=all(len(v)==1 for v in J2img.values())
        if const:
            imgs=[next(iter(v)) for v in J2img.values()]
            nimg=len(set(imgs)); maxf=max(Counter(imgs).values())
            szs=Counter(len(im) if isinstance(im,(frozenset,tuple)) else -1 for im in imgs)
            print(f"    [{name}] const-per-J=True #img={nimg} inj={nimg==OP} maxfiber={maxf} "
                  f"#img<=tgt? {nimg<=tgt} imgsize-dist={dict(sorted(szs.items()))}")
        else:
            nb=sum(1 for v in J2img.values() if len(v)>1)
            print(f"    [{name}] const-per-J=False ({nb}/{OP} J multi-valued)")

if __name__=="__main__":
    LINES={3:(lambda n:(n//2,n//2-1)),4:(lambda n:(n//2+2,n//4+1)),
           5:(lambda n:(n//2+1,n-1)),6:(lambda n:(n//2+4,n//2+2))}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32),(4,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
