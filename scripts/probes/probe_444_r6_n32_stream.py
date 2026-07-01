"""
r=6 n=32 streaming (memory-light): no full cache. One pass over subsets; per subset compute h[0..M]
(M = n-r+1) transiently, evaluate all candidate lines (|e-f| in {1,2,3,4}), accumulate per-line
distinct-gamma sets and S_on_V. Then full report on the maximizer. Target: confirm O_P=185.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter, defaultdict
p=2013265921
def pr(*a): print(*a,flush=True)
def w_of_order(n,P):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return h
    raise RuntimeError

def main():
    import sys
    P=p; n=int(sys.argv[1]) if len(sys.argv)>1 else 32; r=6; a0=7
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    # candidate lines
    lines=[]
    for e in range(r,n):
        for f in range(r,n):
            if f==e: continue
            if abs(e-f) in (1,2,3,4):
                lines.append((e,f))
    M=max(max(e,f) for e,f in lines)-r+1   # max h index needed
    inv_m=[0]+[pow(m,P-2,P) for m in range(1,M+1)]
    pr(f"n={n} r={r}: {len(lines)} candidate lines, M(max h idx)={M}, subsets={comb(n,a0)}")
    # per-line accumulators: per-line fiber Counter (gamma->count), S_on_V, zero, degen
    fibs=[defaultdict(int) for _ in lines]
    son=[0]*len(lines); zero=[0]*len(lines); degen=[0]*len(lines)
    idxs=[(e-r,e-r+1,f-r,f-r+1) for (e,f) in lines]
    invP2=P-2
    cnt=0
    for Sidx in itertools.combinations(range(n),a0):
        # power sums
        PS=[0]*(M+1)
        for i in Sidx:
            z=mu[i]; zi=1
            for j in range(1,M+1): zi=(zi*z)%P; PS[j]=(PS[j]+zi)%P
        h=[0]*(M+1); h[0]=1
        for m in range(1,M+1):
            s=0
            for ii in range(1,m+1): s=(s+PS[ii]*h[m-ii])%P
            h[m]=(s*inv_m[m])%P
        for li,(i1,i2,i3,i4) in enumerate(idxs):
            he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
            if (he_r*hf_r1-hf_r*he_r1)%P!=0: continue
            son[li]+=1
            if hf_r%P!=0: g=(-he_r*pow(hf_r,invP2,P))%P
            elif hf_r1%P!=0: g=(-he_r1*pow(hf_r1,invP2,P))%P
            else: degen[li]+=1; continue
            if g==0: zero[li]+=1; continue
            fibs[li][g]+=1
        cnt+=1
        if cnt%500000==0: pr(f"  ...{cnt} subsets")
    # rank
    res=[]
    for li,(e,f) in enumerate(lines):
        d=gcd((e-f)%n,n); nb=len(fibs[li])
        res.append((nb,e,f,son[li],zero[li],degen[li],d,li))
    res.sort(reverse=True)
    pr("top 8 by #bad:")
    for nb,e,f,sv,z,dg,d,li in res[:8]:
        pr(f"  line(x^{e},x^{f}) d={d}: #bad={nb} S_on_V={sv} O_P={nb//(n//d)} (zero={z},degen={dg})")
    # full fiber report on winner (from accumulated Counter)
    nb,be,bf,bsv,bz,bdg,bd,bli=res[0]
    fs=Counter(fibs[bli].values())
    K=(1<<r)*comb(n//2,r); d=gcd((be-bf)%n,n)
    pr(f"\n>>> MAXIMIZER n={n} r={r} line(x^{be},x^{bf}) e-f={be-bf} d={d} orbit={n//d}")
    pr(f"  (1) #{{S on V}}={bsv}  (nonzero-g={bsv-bz-bdg}, g=0={bz}, degenerate={bdg})")
    pr(f"  (2) #bad={nb}  K={K}  S_on_V<=K:{bsv<=K} ({bsv/K:.4f})  bad/K={nb/K:.4f}")
    pr(f"  (3) fiber sizes {{size:#gamma}}={dict(sorted(fs.items()))}  O_P={nb//(n//d)}")

if __name__=="__main__":
    main()
