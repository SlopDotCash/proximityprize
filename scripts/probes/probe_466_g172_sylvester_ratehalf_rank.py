#!/usr/bin/env python3
"""
OPUS-CORE seam v2: adjudicate SYZ38 SylvesterInjective at rate EXACTLY 1/2.
Fixes v2:
  - CONSTRUCTIVE cover builder that guarantees interior band + genuine 3-support
    (nonempty pairwise-private overlaps AB, AC, BC) so we get real samples.
  - Symbolic check of C1: bAC+bBC < degWAB, expressed via mAB,mAC,mBC,t,k.
  - MASSIVE field-flip sweep of the exact Sylvester matrix rank across primes.

Degrees:  deg W_AB = mAB - t,  deg W_AC = mAC - t,  deg W_BC = mBC - t.
Budgets:  bXY = k - 1 - mXY   (per-pair in-budget cofactor degree cap).
Fable C1: bAC + bBC < degWAB  <=>  (k-1-mAC)+(k-1-mBC) < mAB - t
                              <=>  2k - 2 - mAC - mBC < mAB - t
                              <=>  2k - 2 + t < mAB + mAC + mBC
   Inclusion-exclusion: mAB+mAC+mBC = (union pairwise cover degree). With t=triple,
   and 2k=n, this is  n - 2 + t < mAB+mAC+mBC.
   So C1 <=> mAB+mAC+mBC > n-2+t = 2k-2+t.

We test BOTH: whether C1 holds on real interior covers, AND whether the exact
Sylvester map is injective, AND whether rank flips with the prime.
"""
import random

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                r[i+j]=(r[i+j]+ai*bj)%p
    return r
def poly_mod(a,m,p):
    a=a[:]; dm=len(m)-1; il=pow(m[-1],p-2,p)
    while True:
        while a and a[-1]==0: a.pop()
        if not a or len(a)-1<dm: break
        c=(a[-1]*il)%p; sh=len(a)-1-dm
        for i in range(len(m)):
            a[sh+i]=(a[sh+i]-c*m[i])%p
        while a and a[-1]==0: a.pop()
    return a if a else [0]
def build(roots,p):
    poly=[1]
    for r in roots: poly=poly_mul(poly,[(-r)%p,1],p)
    return poly
def rank_gf(cols,p,ncol):
    mat=[c+[0]*(ncol-len(c)) for c in cols]
    R=len(mat); rank=0
    for col in range(ncol):
        piv=None
        for i in range(rank,R):
            if mat[i][col]%p!=0: piv=i;break
        if piv is None: continue
        mat[rank],mat[piv]=mat[piv],mat[rank]
        inv=pow(mat[rank][col],p-2,p)
        mat[rank]=[(x*inv)%p for x in mat[rank]]
        for i in range(R):
            if i!=rank and mat[i][col]%p:
                f=mat[i][col]
                mat[i]=[(mat[i][j]-f*mat[rank][j])%p for j in range(ncol)]
        rank+=1
        if rank==R: break
    return rank
def sylv_kernel(WAB,WAC,WBC,bAC,bBC,p):
    dW=len(WAB)-1
    cols=[]
    for i in range(bAC+1):
        v=poly_mod(poly_mul(WAC,[0]*i+[1],p),WAB,p); cols.append((v+[0]*dW)[:dW])
    for j in range(bBC+1):
        v=poly_mod(poly_mul([(-c)%p for c in WBC],[0]*j+[1],p),WAB,p); cols.append((v+[0]*dW)[:dW])
    return len(cols)-rank_gf(cols,p,dW)

def construct_cover(n,s,seed):
    """Build 3 s-subsets of [n] with a controlled triple overlap t and genuine
    private pairwise overlaps. Return sets A,B,C or None."""
    rng=random.Random(seed)
    pts=list(range(n))
    # pick triple core T, and private pairwise chunks, sized to keep |X|=s
    # |A| = t + |AB'| + |AC'| + privA  (AB' = A&B minus T, etc.)
    for _ in range(30):
        t=rng.randint(1, max(1,s//3))
        abp=rng.randint(1, max(1,s//3))
        acp=rng.randint(1, max(1,s//3))
        bcp=rng.randint(1, max(1,s//3))
        # A = T + AB' + AC' + privA  => privA = s - t - abp - acp
        pa=s-t-abp-acp; pb=s-t-abp-bcp; pc=s-t-acp-bcp
        if pa<0 or pb<0 or pc<0: continue
        need=t+abp+acp+bcp+pa+pb+pc
        if need>n: continue
        pool=rng.sample(pts,need)
        it=iter(pool)
        T=[next(it) for _ in range(t)]
        AB=[next(it) for _ in range(abp)]
        AC=[next(it) for _ in range(acp)]
        BC=[next(it) for _ in range(bcp)]
        PA=[next(it) for _ in range(pa)]
        PB=[next(it) for _ in range(pb)]
        PC=[next(it) for _ in range(pc)]
        A=set(T+AB+AC+PA); B=set(T+AB+BC+PB); C=set(T+AC+BC+PC)
        if len(A)==s and len(B)==s and len(C)==s:
            return A,B,C
    return None

def main():
    primes=[31,101,257,1009,65537]
    print("=== SYZ38 SylvesterInjective @ rate EXACTLY 1/2 — constructive sweep ===")
    total_c1_fail=0; total_ker_pos=0; flips=[]; valid=0
    c1_margin_hist={}
    for n in [12,16,20,24,28,32]:
        k=n//2
        for s in range(2*n//3+1, (3*n+3)//4):
            for seed in range(400):
                cov=construct_cover(n,s,seed)
                if cov is None: continue
                A,B,C=cov
                mAB=len(A&B);mAC=len(A&C);mBC=len(B&C);t=len(A&B&C)
                bAC=k-1-mAC; bBC=k-1-mBC; bAB=k-1-mAB
                if bAC<0 or bBC<0 or bAB<0: continue
                degWAB=mAB-t
                if degWAB<=0: continue
                # need genuine 3-support window: bAC>=0,bBC>=0 already; also private overlaps nonempty
                if mAB<=t or mAC<=t or mBC<=t: continue
                valid+=1
                c1=(bAC+bBC)<degWAB
                margin=degWAB-(bAC+bBC)  # >0 means C1 holds
                c1_margin_hist[margin]=c1_margin_hist.get(margin,0)+1
                if not c1: total_c1_fail+=1
                # exact Sylvester rank per prime (fixed combinatorics, roots = distinct field elts)
                kds={}
                for p in primes:
                    rng=random.Random(seed*1000+7)
                    # skip ONLY primes too small to host n distinct labels; keep the
                    # cover and evaluate over the remaining (larger) primes.
                    if p-1 < n: continue
                    labels=rng.sample(range(1,p),n)
                    # relabel using full index set [n]
                    lab={x:labels[x] for x in range(n)}
                    WAB=build([lab[x] for x in (A&B)-(A&B&C)],p)
                    WAC=build([lab[x] for x in (A&C)-(A&B&C)],p)
                    WBC=build([lab[x] for x in (B&C)-(A&B&C)],p)
                    kds[p]=sylv_kernel(WAB,WAC,WBC,bAC,bBC,p)
                if not kds: continue
                if any(v>0 for v in kds.values()): total_ker_pos+=1
                if len(set(kds.values()))>1:
                    flips.append((n,k,s,seed,mAB,mAC,mBC,t,bAC,bBC,degWAB,dict(kds)))
    print(f"valid rate-1/2 3-support covers tested: {valid}")
    print(f"C1 (bAC+bBC < degWAB, Fable summed-budget) FAILURES: {total_c1_fail}")
    print(f"  C1 margin histogram (degWAB-(bAC+bBC)): {dict(sorted(c1_margin_hist.items()))}")
    print(f"SylvesterInjective FALSE (positive kernel) instances: {total_ker_pos}")
    print(f"FIELD-FLIP instances (kernel dim varies across primes): {len(flips)}")
    for f in flips[:20]: print("  FLIP",f)

if __name__=="__main__":
    main()
