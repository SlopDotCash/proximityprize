"""
Reconcile the Schur-h_m bad-set definition against the interpolation definition (probe_444_antipodal).
Goal: confirm that for an (r+1)-subset S, the genuine "bad for line (x^e,x^f)" event matches
   h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S)   AND the pinned gamma matches.
We compute gamma both ways for ALL subsets and report agreement, separating the gamma=0 cases.
"""
import itertools
from math import comb, gcd
from collections import Counter

p = 2013265921

def w_of_order(n, pr):
    e=(pr-1)//n
    for c in range(2,2000):
        h=pow(c,e,pr)
        if pow(h,n,pr)==1 and pow(h,n//2,pr)!=1: return h
    raise RuntimeError

def interp_coeffs(pts, vals, pr):
    m=len(pts)
    M=[[pow(pts[i],j,pr) for j in range(m)]+[vals[i]%pr] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%pr!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        invp=pow(M[col][col],pr-2,pr); M[col]=[(v*invp)%pr for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%pr!=0:
                fc=M[rr][col]; M[rr]=[(M[rr][k]-fc*M[col][k])%pr for k in range(m+1)]
    return [M[i][m]%pr for i in range(m)]

def gamma_interp(pts,e,f,k,a0,pr):
    c0=interp_coeffs(pts,[pow(t,e,pr) for t in pts],pr)
    c1=interp_coeffs(pts,[pow(t,f,pr) for t in pts],pr)
    if c0 is None or c1 is None: return ('deg',None)
    gam=None; nd=False
    for j in range(k,a0):
        x0=c0[j]; x1=c1[j]
        if x0 or x1: nd=True
        if x1==0:
            if x0: return ('no',None)
        else:
            g=(-x0*pow(x1,pr-2,pr))%pr
            if gam is None: gam=g
            elif gam!=g: return ('no',None)
    if not nd: return ('no',None)
    return ('bad', gam if gam is not None else 0)

def complete_homog(S, mmax, pr):
    P=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1):
            zi=(zi*z)%pr; P[j]=(P[j]+zi)%pr
    h=[0]*(mmax+1); h[0]=1
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+P[i]*h[m-i])%pr
        h[m]=(s*pow(m,pr-2,pr))%pr
    return h

def gamma_schur(S,e,f,r,pr):
    mmax=max(e-r,e-r+1,f-r,f-r+1)
    h=complete_homog(S,mmax,pr)
    he_r=h[e-r];he_r1=h[e-r+1];hf_r=h[f-r];hf_r1=h[f-r+1]
    on_v = (he_r*hf_r1 - hf_r*he_r1)%pr==0
    if not on_v: return ('no',None)
    if hf_r%pr!=0:
        return ('bad', (-he_r*pow(hf_r,pr-2,pr))%pr)
    if hf_r1%pr!=0:
        return ('bad', (-he_r1*pow(hf_r1,pr-2,pr))%pr)
    return ('bad', 0)  # fully degenerate

def compare(n,r,e,f,pr=p):
    w=w_of_order(n,pr); mu=[pow(w,i,pr) for i in range(n)]
    k=r-1; a0=r+1
    agree=0; disagree=[]; both_bad=0
    cnt_i=Counter(); cnt_s=Counter()
    gi_nz=set(); gs_nz=set(); gi_zero=0; gs_zero=0
    for Sidx in itertools.combinations(range(n),a0):
        pts=[mu[i] for i in Sidx]
        ti,gi = gamma_interp(pts,e,f,k,a0,pr)
        ts,gs = gamma_schur(pts,e,f,r,pr)
        cnt_i[ti]+=1; cnt_s[ts]+=1
        if ti=='bad':
            if gi==0: gi_zero+=1
            else: gi_nz.add(gi)
        if ts=='bad':
            if gs==0: gs_zero+=1
            else: gs_nz.add(gs)
    print(f"n={n} r={r} line(x^{e},x^{f}):")
    print(f"  interp: {dict(cnt_i)}   #bad_nz(distinct)={len(gi_nz)} zero_subsets={gi_zero}")
    print(f"  schur : {dict(cnt_s)}   #bad_nz(distinct)={len(gs_nz)} zero_subsets={gs_zero}")
    print(f"  distinct-nz-gamma sets equal: {gi_nz==gs_nz}")

for n in [16]:
    compare(n,3,n//2,n//2-1)
    compare(n,4,n//2,n//2-3)
