"""
probe_444_angleC_n32fast.py -- numpy-vectorized all-line check of  O_P <= C(n/2, r-1)  at n=32.
Single prime (BabyBear). Precompute h-vectors for ALL (r+1)-subsets via numpy, then per-line
vectorized det-check + gamma + coset.  Confirms the crude bound across EVERY admissible line.
"""
import sys, numpy as np
from math import comb, gcd
from itertools import combinations

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def inv_mod(a,p=P):
    # vectorized modular inverse via Fermat (a^(p-2)); a is np.int64 array. Use pow per-element in py for safety.
    return np.array([pow(int(x),p-2,p) if x%p else 0 for x in a],dtype=object)

def build_H(n,r,p=P):
    """For all (r+1)-subsets, compute H[m] for m=0..n.  Returns array shape (Nsub, n+1) as python ints (object)."""
    w=gen(n,p); a0=r+1
    wp=[pow(w,i,p) for i in range(n)]
    subs=list(combinations(range(n),a0))
    Nsub=len(subs)
    Hmax=n
    # power sums P_i for each subset: P[i]=sum x^i. Precompute x^i for all elements: pw_pow[elem][i]
    # elements are wp[idx]; powers up to Hmax. Build table powtab[idx][i]=wp[idx]^i mod p.
    powtab=[[1]*(Hmax+1) for _ in range(n)]
    for idx in range(n):
        for i in range(1,Hmax+1):
            powtab[idx][i]=powtab[idx][i-1]*wp[idx]%p
    invm=[pow(m,p-2,p) for m in range(1,Hmax+1)]
    H=np.empty((Nsub,Hmax+1),dtype=object)
    for si,S in enumerate(subs):
        Ps=[0]*(Hmax+1)
        for i in range(1,Hmax+1):
            s=0
            for idx in S: s+=powtab[idx][i]
            Ps[i]=s%p
        Hrow=[0]*(Hmax+1); Hrow[0]=1
        for m in range(1,Hmax+1):
            s=0
            for i in range(1,m+1): s+=Ps[i]*Hrow[m-i]
            Hrow[m]=s%p*invm[m-1]%p
        H[si]=Hrow
    return H, Nsub

def scan(n,r,H,Nsub,p=P):
    bound=comb(n//2,r-1) if n//2>=r-1 else 0
    worst=(0.0,None,0,0); allok=True
    for e in range(r,n):
        for f in range(r,n):
            if e==f: continue
            er,fr,er1,fr1=e-r,f-r,e-r+1,f-r+1
            if max(er1,fr1)>n: continue
            d=gcd((e-f)%n,n); nd=n//d
            cos=set()
            for si in range(Nsub):
                Her,Her1,Hfr,Hfr1=H[si][er],H[si][er1],H[si][fr],H[si][fr1]
                if (Her*Hfr1-Hfr*Her1)%p: continue
                if Hfr==0: continue
                g=(-Her*pow(int(Hfr),p-2,p))%p
                if g: cos.add(pow(int(g),nd,p))
            OP=len(cos)
            if OP>bound: allok=False
            ratio=OP/bound if bound else 0
            if ratio>worst[0]: worst=(ratio,(e,f),OP,d)
    return bound,worst,allok

if __name__=="__main__":
    todo=[(3,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        print(f"building H for r={r} n={n}...",flush=True)
        H,Nsub=build_H(n,r)
        bound,worst,allok=scan(n,r,H,Nsub)
        print(f"r={r} n={n}: C(n/2,r-1)={bound}  max O_P/bound={worst[0]:.3f} at {worst[1]} O_P={worst[2]} d={worst[3]}  ALL O_P<=C(n/2,r-1)? {allok}",flush=True)
