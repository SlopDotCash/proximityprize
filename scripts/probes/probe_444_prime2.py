"""
Cross-check the chain-break (x^20,x^16) and maximizer (x^20,x^18) at n=32 over a SECOND prime
(3221225473, 2^30|p-1) using the Schur-V count + degen separation (fast). genuine ~ Schur_V - degen.
If the d=4 break persists over both primes, it is char-0 structural (not a char-p coincidence).
"""
import itertools, sys
from math import comb, gcd
p2=3221225473
def pr(*a): print(*a,flush=True)
def w_of_order(n,P):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return h
    raise RuntimeError
def line_schur(n,r,e,f,P):
    a0=r+1; i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1; M=max(i1,i2,i3,i4)
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    inv_m=[0]+[pow(m,P-2,P) for m in range(1,M+1)]
    son=0; degen=0; zero=0; nz=set()
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
        he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
        if (he_r*hf_r1-hf_r*he_r1)%P!=0: continue
        son+=1
        if hf_r%P!=0: g=(-he_r*pow(hf_r,invP2,P))%P
        elif hf_r1%P!=0: g=(-he_r1*pow(hf_r1,invP2,P))%P
        else: degen+=1; continue
        if g==0: zero+=1
        else: nz.add(g)
    K=(1<<r)*comb(n//2,r); d=gcd((e-f)%n,n)
    genuine_est=son-degen
    pr(f"  P={P} line(x^{e},x^{f}) d={d}: SchurV={son} degen={degen} genuine_est={genuine_est} "
       f"zero={zero} #bad={len(nz)} K={K} genuine<=K:{genuine_est<=K}({genuine_est/K:.4f}) O_P={len(nz)//(n//d)}")

if __name__=="__main__":
    n=32; r=6
    pr("=== SECOND PRIME 3221225473 cross-check (Schur-V, genuine_est=SchurV-degen) ===")
    which=sys.argv[1] if len(sys.argv)>1 else "break"
    if which=="break": line_schur(n,r,20,16,p2)
    else: line_schur(n,r,20,18,p2)
