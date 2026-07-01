"""
VERIFY the crude-chain breakage: does any admissible r=6 line have #{S on V} > K at n=32?
Found x^20,x^16 (d=4): S_on_V=560608 > K=512512. Double-check via INDEPENDENT interpolation
definition (not the Schur identity) on a sample + recount S_on_V via Schur to confirm exact integer.
Also report the maximizer of S_on_V over a broader e-f scan (d in {1..8}) to find the worst chain ratio.
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

def interp_coeffs(pts, vals, P):
    m=len(pts)
    M=[[pow(pts[i],j,P) for j in range(m)]+[vals[i]%P] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%P!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        invp=pow(M[col][col],P-2,P); M[col]=[(v*invp)%P for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%P!=0:
                fc=M[rr][col]; M[rr]=[(M[rr][k]-fc*M[col][k])%P for k in range(m+1)]
    return [M[i][m]%P for i in range(m)]

def bad_interp(pts,e,f,k,a0,P):
    c0=interp_coeffs(pts,[pow(t,e,P) for t in pts],P)
    c1=interp_coeffs(pts,[pow(t,f,P) for t in pts],P)
    if c0 is None or c1 is None: return False
    gam=None; nd=False
    for j in range(k,a0):
        x0=c0[j];x1=c1[j]
        if x0 or x1: nd=True
        if x1==0:
            if x0: return False
        else:
            g=(-x0*pow(x1,P-2,P))%P
            if gam is None: gam=g
            elif gam!=g: return False
    return nd

def main():
    n=32; r=6; a0=7; k=r-1; P=p; K=(1<<r)*comb(n//2,r)
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    # CONFIRM x^20,x^16 S_on_V via BOTH Schur and interpolation on a sample, and exact Schur count.
    e,f=20,16; i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1; M=max(i1,i2,i3,i4)
    inv_m=[0]+[pow(m,P-2,P) for m in range(1,M+1)]
    son=0; agree=0; tot=0; disagree=0
    import random
    random.seed(1)
    allc=itertools.combinations(range(n),a0)
    # exact Schur count + spot-check interpolation on 3000 random subsets
    sample_idx=set(random.sample(range(comb(n,a0)),3000))
    ci=0
    for Sidx in itertools.combinations(range(n),a0):
        S=[mu[i] for i in Sidx]
        PS=[0]*(M+1)
        for z in S:
            zi=1
            for j in range(1,M+1): zi=(zi*z)%P; PS[j]=(PS[j]+zi)%P
        h=[0]*(M+1); h[0]=1
        for m in range(1,M+1):
            s=0
            for ii in range(1,m+1): s=(s+PS[ii]*h[m-ii])%P
            h[m]=(s*inv_m[m])%P
        onv = (h[i1]*h[i4]-h[i2]*h[i3])%P==0
        if onv: son+=1
        if ci in sample_idx:
            bi=bad_interp(S,e,f,k,a0,P)
            if bi==onv: agree+=1
            else: disagree+=1
            tot+=1
        ci+=1
    pr(f"n={n} r={r} line(x^{e},x^{f}) d={gcd((e-f)%n,n)}:")
    pr(f"  EXACT #{{S on V}} (Schur) = {son}   K={K}   S_on_V>K: {son>K}  ratio={son/K:.4f}")
    pr(f"  interpolation-vs-Schur agreement on {tot} sampled subsets: agree={agree} disagree={disagree}")

if __name__=="__main__":
    main()
