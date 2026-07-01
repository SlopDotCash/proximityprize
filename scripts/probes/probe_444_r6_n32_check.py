"""
n=32 r=6: check specific lines to reconcile CONTEXT O_P=185 vs found O_P=203.
Check x^24,x^22 (3n/4 analog), x^20,x^18 (found max), and a few |e-f|>4 lines, plus the r=5/r=6
CONTEXT maximizer (x^{n/2+1},x^{n-1}) style. Streaming single-line eval (memory light).
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

def eval_lines(n,r,lines,P):
    a0=r+1
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    M=max(max(e,f) for e,f in lines)-r+1
    inv_m=[0]+[pow(m,P-2,P) for m in range(1,M+1)]
    idxs=[(e-r,e-r+1,f-r,f-r+1) for e,f in lines]
    fibs=[defaultdict(int) for _ in lines]
    son=[0]*len(lines); zero=[0]*len(lines); degen=[0]*len(lines)
    invP2=P-2
    for Sidx in itertools.combinations(range(n),a0):
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
    out=[]
    for li,(e,f) in enumerate(lines):
        d=gcd((e-f)%n,n); nb=len(fibs[li])
        out.append((e,f,nb,son[li],zero[li],degen[li],d,nb//(n//d),Counter(fibs[li].values())))
    return out

if __name__=="__main__":
    n=32; r=6; P=p
    # lines to check: 3n/4 analog, found max, several e-f and positions
    lines=[(24,22),(22,24),(20,18),(24,26),(28,26),(22,20),(20,22),
           (20,16),(24,20),(31,7),(17,31),(16,14),(26,24)]
    res=eval_lines(n,r,lines,P)
    K=(1<<r)*comb(n//2,r)
    pr(f"n={n} r={r} K={K} C(n,r+1)={comb(n,r+1)}")
    res.sort(key=lambda t:-t[2])
    for e,f,nb,sv,z,dg,d,op,fs in res:
        pr(f"  line(x^{e},x^{f}) d={d}: #bad={nb} O_P={op} S_on_V={sv} (z={z},dg={dg}) "
           f"S_on_V<=K:{sv<=K}({sv/K:.3f}) fibers={dict(sorted(fs.items()))}")
