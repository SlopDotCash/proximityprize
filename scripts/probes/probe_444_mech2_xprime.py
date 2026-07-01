"""
probe_444_mech2_xprime.py -- cross-prime (char-0) confirmation of the Mechanism-2 verdict:
  (1) the within-part / difference-set index map is constant-per-J at r=3,4 (opp parity) but lossy;
  (2) it FAILS constancy at r=5 same-parity;
  (3) O_P matches across both primes (=> char-0, structural not arithmetic-accident).
Run on BOTH primes.
"""
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
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
def collect(n,r,e,f,p):
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

def run(p):
    LINES={3:(lambda n:(n//2,n//2-1)),4:(lambda n:(n//2+2,n//4+1)),
           5:(lambda n:(n//2+1,n-1)),6:(lambda n:(n//2+4,n//2+2))}
    print(f"# prime p={p}")
    for (r,n) in [(3,16),(4,16),(5,16),(6,16),(3,32)]:
        e,f=LINES[r](n); w,J2S,d,nd=collect(n,r,e,f,p)
        OP=len(J2S)
        def fold(x): return min(x%n,(-x)%n)
        ds=lambda S:frozenset(fold(i-j) for i in S for j in S if i!=j)
        J2img=defaultdict(set)
        for J,Ss in J2S.items():
            for S in Ss: J2img[J].add(ds(sorted(S)))
        const=all(len(v)==1 for v in J2img.values())
        nimg=len(set(next(iter(v)) for v in J2img.values())) if const else -1
        maxf=Counter(next(iter(v)) for v in J2img.values()).most_common(1)[0][1] if const else -1
        print(f"  r={r} n={n}: O_P={OP} C(n/2,r-1)={comb(n//2,r-1)} | diffset const-per-J={const} "
              f"#img={nimg} maxfiber={maxf} inj={nimg==OP}")

if __name__=="__main__":
    for p in (2013265921, 3221225473):
        run(p); print()
