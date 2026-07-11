#!/usr/bin/env python3
"""
CRUX: at rate 1/2, is d1 (minimal syzygy degree) ALWAYS > budget=k-1-t, even under maximal
mu-basis imbalance? Two quantities:
  balanced_d1 = floor((a+b+c)/2)
  imbalance   = balanced_d1 - actual_d1  (>=0; how far below balanced the module sits)
  margin      = actual_d1 - budget
We saw imbalance in {0,1} so far and margin>=1. The question: can imbalance be large enough
(driven by resultant vanishing / structured roots) to push actual_d1 <= budget?

Lower bound theory: for a pairwise-coprime triple mapping onto K[X], the syzygy module is
rank-2 free with degrees d1<=d2, d1+d2 = a+b+c. The SMALLEST possible d1 is bounded below by
a+b+c - d2_max. d2 <= a+b+c (max cofactor). But sharper: the 2-support Koszul syzygies give
generators of degree a+b, a+c, b+c (support-2, coprime pair (W_i,W_j) => (W_j,W_i) syzygy of
product-degree deg W_i+deg W_j). The module contains these; a minimal generator d1 <= min(a+b,a+c,b+c).
Lower bound on d1: any syzygy is (rAB,rAC,rBC) with W_AB rAB - W_AC rAC + W_BC rBC=0. If rAB!=0
then deg(W_AB rAB)=a+deg rAB must be matched by RHS <= max(b+deg rAC, c+deg rBC) <= D. So all
present terms have product-degree = D (the top). At degree D a nonzero syzygy needs the top
coefficients to cancel: at least TWO of the three cofactors nonzero at top degree. So
D >= second-smallest of {a,b,c}? No... The rigorous lower bound: a nonzero syzygy of product
degree D has >=2 nonzero terms at degree D, so D >= (a + b + c) - max - ...

We measure the EXTREME: over structured/adversarial roots (subfield-confined, geometric,
resultant-tuned), the MINIMUM d1 observed, and the MINIMUM margin. If min margin >= 1 across a
large adversarial sweep, SylvesterInjective at rate 1/2 is robustly TRUE with a provable slack;
report the exact worst-case imbalance.
"""
import random
def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r
def build(roots,p):
    poly=[1]
    for r in roots: poly=poly_mul(poly,[(-r)%p,1],p)
    return poly
def deg(a):
    a=list(a)
    while a and a[-1]==0: a.pop()
    return len(a)-1 if a else -1
def rank_gf(rows,p,ncol):
    mat=[c+[0]*(ncol-len(c)) for c in rows]; R=len(mat); rank=0
    for col in range(ncol):
        piv=None
        for i in range(rank,R):
            if mat[i][col]%p!=0: piv=i;break
        if piv is None: continue
        mat[rank],mat[piv]=mat[piv],mat[rank]
        inv=pow(mat[rank][col],p-2,p); mat[rank]=[(x*inv)%p for x in mat[rank]]
        for i in range(R):
            if i!=rank and mat[i][col]%p:
                f=mat[i][col]; mat[i]=[(mat[i][j]-f*mat[rank][j])%p for j in range(ncol)]
        rank+=1
        if rank==R: break
    return rank
def kdim(WAB,WAC,WBC,p,D):
    dAB,dAC,dBC=deg(WAB),deg(WAC),deg(WBC)
    cols=[]
    for i in range(max(D-dAB+1,0)): cols.append((poly_mul(WAB,[0]*i+[1],p)+[0]*(D+1))[:D+1])
    for i in range(max(D-dAC+1,0)): cols.append((poly_mul([(-c)%p for c in WAC],[0]*i+[1],p)+[0]*(D+1))[:D+1])
    for i in range(max(D-dBC+1,0)): cols.append((poly_mul(WBC,[0]*i+[1],p)+[0]*(D+1))[:D+1])
    nunk=len(cols)
    if not nunk: return 0
    rows=[[cols[j][r] for j in range(nunk)] for r in range(D+1)]
    return nunk-rank_gf(rows,p,nunk)
def d1_of(WAB,WAC,WBC,p,dmax):
    for D in range(dmax+1):
        if kdim(WAB,WAC,WBC,p,D)>=1: return D
    return -1
def construct_cover(n,s,seed):
    rng=random.Random(seed); pts=list(range(n))
    for _ in range(40):
        t=rng.randint(1,max(1,s//3)); abp=rng.randint(1,max(1,s//3))
        acp=rng.randint(1,max(1,s//3)); bcp=rng.randint(1,max(1,s//3))
        pa=s-t-abp-acp; pb=s-t-abp-bcp; pc=s-t-acp-bcp
        if pa<0 or pb<0 or pc<0: continue
        need=t+abp+acp+bcp+pa+pb+pc
        if need>n: continue
        pool=rng.sample(pts,need); it=iter(pool)
        T=[next(it) for _ in range(t)];AB=[next(it) for _ in range(abp)]
        AC=[next(it) for _ in range(acp)];BC=[next(it) for _ in range(bcp)]
        PA=[next(it) for _ in range(pa)];PB=[next(it) for _ in range(pb)];PC=[next(it) for _ in range(pc)]
        A=set(T+AB+AC+PA);B=set(T+AB+BC+PB);C=set(T+AC+BC+PC)
        if len(A)==s and len(B)==s and len(C)==s: return A,B,C
    return None
def adversarial_labels(n,p,seed,mode):
    rng=random.Random(seed)
    if mode=='generic': return rng.sample(range(1,p),n)
    if mode=='ap': a0=rng.randrange(1,p); d=rng.randrange(1,p);
    if mode=='ap': return [(a0+d*i)%p for i in range(n)]
    if mode=='geom':
        g=rng.randrange(2,p); return [pow(g,i,p) for i in range(n)]
    if mode=='subfield' and (p==257):
        # GF(257) has subfield only GF(257); use small window instead
        return rng.sample(range(1,min(p,40)),n) if min(p,40)>n else rng.sample(range(1,p),n)
    if mode=='clustered':
        base=rng.sample(range(1,p),3); out=[]
        while len(out)<n:
            b=rng.choice(base); out.append((b+rng.randrange(-2,3))%p or 1)
        return list(dict.fromkeys(out))[:n] if len(set(out))>=n else rng.sample(range(1,p),n)
    return rng.sample(range(1,p),n)
def main():
    primes=[101,257,1009,65537]
    print("=== worst-case margin: min(d1-budget) and max imbalance under adversarial roots ===")
    tot=0; min_margin=999; max_imb=0; worst=[]; inbud=0
    for n in [16,20,24,28,32,36,40,48,56]:
        k=n//2
        for s in range(2*n//3+1,(3*n+3)//4):
            for seed in range(500):
                cov=construct_cover(n,s,seed)
                if cov is None: continue
                A,B,C=cov
                mAB=len(A&B);mAC=len(A&C);mBC=len(B&C);t=len(A&B&C)
                if mAB<=t or mAC<=t or mBC<=t: continue
                a,b,c=mAB-t,mAC-t,mBC-t
                budget=k-1-t; bal=(a+b+c)//2
                for p in primes:
                    for mi,mode in enumerate(['generic','ap','geom','clustered']):
                        # fixed per-mode offset (NOT Python's salted hash) so runs are
                        # bit-for-bit reproducible regardless of PYTHONHASHSEED.
                        lab=adversarial_labels(n,p,seed*13+mi*101+17,mode)
                        if len(set(lab))<n: continue
                        try:
                            WAB=build([lab[x] for x in (A&B)-(A&B&C)],p)
                            WAC=build([lab[x] for x in (A&C)-(A&B&C)],p)
                            WBC=build([lab[x] for x in (B&C)-(A&B&C)],p)
                        except Exception: continue
                        if deg(WAB)!=a or deg(WAC)!=b or deg(WBC)!=c: continue
                        # coprimality: root sets disjoint by construction, ok
                        tot+=1
                        d1=d1_of(WAB,WAC,WBC,p,a+b+c+1)
                        if d1<0: continue
                        margin=d1-budget; imb=bal-d1
                        if margin<min_margin: min_margin=margin;
                        if imb>max_imb: max_imb=imb
                        if margin<=0: inbud+=1; worst.append((n,k,s,t,a,b,c,d1,budget,bal,p,mode))
                        elif margin==1 and imb>=1:
                            if len(worst)<10: worst.append(('tight',n,k,s,t,a,b,c,d1,budget,bal,p,mode))
    print(f"triples evaluated: {tot}")
    print(f"  MIN margin (d1-budget): {min_margin}   (>=1 => SylvesterInjective robustly true)")
    print(f"  MAX imbalance (floor((a+b+c)/2)-d1): {max_imb}")
    print(f"  in-budget (SylvesterInjective FALSE) count: {inbud}")
    for w in worst[:20]: print("   ",w)
if __name__=="__main__": main()
