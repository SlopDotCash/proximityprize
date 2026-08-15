#!/usr/bin/env python3
"""Is sign-discordance of (A_5,A_6) confined to a near-threshold band?

From oc_joint_sign_probe: sign(A5)==sign(A6) in 212/218 primes. The 6
discordant cases have conspicuously SMALL minor-rank magnitude (e.g. p=89
A6=40 vs concordant A6 ~ 1e7). Hypothesis (bindable invariant):

  H: discordance => min(|rho_5|,|rho_6|) < tau   (correlation-threshold)
     equivalently the flipped rank sits inside the Parseval near-null band.

If TRUE with a clean tau bounded away from the concordant band, we get a
theorem-shaped statement:
   "outside a measure-shrinking near-null correlation band, sign(A_5)=sign(A_6),
    but the band is non-empty -> no unconditional single-rank reduction, and
    the ONLY obstruction to concordance is small-|rho| cancellation."
That is a genuine JOINT-placement invariant, not a support statistic.

We compute rho_r = A_r / sqrt(centeredW * centeredR_r) for every prime and
tabulate min(|rho5|,|rho6|) split by concordant/discordant.
"""
from __future__ import annotations
import math, numpy as np

def factor(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out
def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise ValueError(p)
def subgroup(p,n):
    z=pow(primitive_root(p),(p-1)//n,p); G=[]; x=1
    for _ in range(n): G.append(x); x=x*z%p
    return G
def subset_hists(G,p,R):
    dp=np.zeros((R+1,p),dtype=object); dp[0,0]=1; used=0
    for x in G:
        used+=1
        for k in range(min(R,used),0,-1): dp[k]=dp[k]+np.roll(dp[k-1],x)
    return dp
def circ_corr_exact(a,b,p):
    a=[int(v) for v in a]; b=[int(v) for v in b]; c=[0]*p
    nz=[(x,a[x]) for x in range(p) if a[x]]
    for t in range(p):
        s=0
        for x,av in nz:
            bv=b[(x-t)%p]
            if bv: s+=av*bv
        c[t]=s
    return c
def rho_A(G,p,n,r):
    dp=subset_hists(G,p,r); W=[0]*p
    for y in G:
        y2=(2*y)%p
        for z in G: W[(y2-z)%p]+=1
    R=circ_corr_exact(dp[r],dp[r-1],p)
    totalR=math.comb(n,r)*math.comb(n,r-1)
    C12=sum(W[t]*R[t] for t in range(p))
    A=p*C12-n*n*totalR
    cW=p*sum(x*x for x in W)-n**4
    cR=p*sum(x*x for x in R)-totalR*totalR
    rho=A/math.sqrt(cW*cR) if cW>0 and cR>0 else 0.0
    return A, rho
def primes_with_order(n, lo, hi):
    out=[]; x=lo|1
    while x<=hi:
        if x>=5 and all(x%q for q in range(2,int(x**0.5)+1)) and (x-1)%n==0: out.append(x)
        x+=2
    return out
def v2(m): return (m&-m).bit_length()-1

def main():
    conc=[]; disc=[]
    for n in (8,16,32):
        for p in primes_with_order(n,5, 4000 if n<32 else 3000):
            G=subgroup(p,n)
            A5,r5=rho_A(G,p,n,5); A6,r6=rho_A(G,p,n,6)
            mmin=min(abs(r5),abs(r6)); mmax=max(abs(r5),abs(r6))
            rec=(n,p,v2(p-1),A5,A6,r5,r6,mmin,mmax)
            if (A5>0)==(A6>0) and A5!=0 and A6!=0: conc.append(rec)
            else: disc.append(rec)
    def stats(L):
        if not L: return (float('nan'),)*4
        ms=[r[7] for r in L]
        return (min(ms),max(ms),sum(ms)/len(ms),sorted(ms)[len(ms)//2])
    cmin,cmax,cavg,cmed=stats(conc)
    dmin,dmax,davg,dmed=stats(disc)
    print(f"concordant n={len(conc)}: min|rho|_min={cmin:.4f} max={cmax:.4f} avg={cavg:.4f} med={cmed:.4f}")
    print(f"discordant n={len(disc)}: min|rho|_min={dmin:.4f} max={dmax:.4f} avg={davg:.4f} med={dmed:.4f}")
    print("\nDISCORDANT detail (sorted by min|rho|):")
    for r in sorted(disc,key=lambda z:z[7]):
        print(f"  n={r[0]} p={r[1]} v2={r[2]} rho5={r[5]:+.5f} rho6={r[6]:+.5f} min|rho|={r[7]:.5f}")
    # threshold separation test
    dmax_ = max((r[7] for r in disc), default=0)
    conc_below = [r for r in conc if r[7] <= dmax_]
    print(f"\nmax discordant min|rho| = {dmax_:.5f}")
    print(f"concordant primes with min|rho| <= that threshold: {len(conc_below)} / {len(conc)}")
    if conc_below:
        print("  -> band is NOT clean; concordant cases also fall in low-|rho| band:")
        for r in sorted(conc_below,key=lambda z:z[7])[:12]:
            print(f"     n={r[0]} p={r[1]} min|rho|={r[7]:.5f} rho5={r[5]:+.4f} rho6={r[6]:+.4f}")
    else:
        print("  -> CLEAN separation: all discordance strictly inside a low-|rho| band")
    # what fraction of low-band is discordant
    thr=0.10
    low=[r for r in conc+disc if r[7]<thr]
    lowd=[r for r in low if r in disc]
    print(f"\nlow-band |rho|<{thr}: total={len(low)} discordant={len(lowd)} rate={len(lowd)/max(len(low),1):.3f}")

if __name__=='__main__': main()
