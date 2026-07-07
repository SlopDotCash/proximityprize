"""
probe_444_r6_full.py -- #444 MEASURE r=6 (final). Caches h-vectors once per subset.
Reports, for the TRUE r=6 maximizer line at n=16,32 (and 64 if feasible):
 (1) #{S on V} = number of bad (r+1)-subsets (the variety V membership count)
 (2) #bad = #distinct nonzero gamma ; K = 2^r C(n/2,r) ; check #{S on V}<=K and #bad<=#{S on V}
 (3) gamma-fiber size distribution
 (4) structure of V (degeneracy split, e-f, d, orbit size)
Reproduces r=3 calibration first.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter, defaultdict
p=2013265921
p2=3221225473

def w_of_order(n,pr):
    e=(pr-1)//n
    for c in range(2,4000):
        h=pow(c,e,pr)
        if pow(h,n,pr)==1 and pow(h,n//2,pr)!=1: return h
    raise RuntimeError("no w")

def build_h_cache(n,a0,mmax,mu,pr):
    """Return dict Sidx->h[0..mmax]. h via complete homogeneous from power sums."""
    cache={}
    inv_m=[0]+[pow(m,pr-2,pr) for m in range(1,mmax+1)]
    for Sidx in itertools.combinations(range(n),a0):
        P=[0]*(mmax+1)
        for i in Sidx:
            z=mu[i]; zi=1
            for j in range(1,mmax+1):
                zi=(zi*z)%pr; P[j]=(P[j]+zi)%pr
        h=[0]*(mmax+1); h[0]=1
        for m in range(1,mmax+1):
            s=0
            for ii in range(1,m+1): s=(s+P[ii]*h[m-ii])%pr
            h[m]=(s*inv_m[m])%pr
        cache[Sidx]=h
    return cache

def analyze_line(n,r,e,f,cache,mu,pr,want_fibers=True):
    a0=r+1
    i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1
    d=gcd((e-f)%n,n); mult=pow(mu[1] if False else None,0,pr) if False else None
    # mult = generator^(e-f): mu[i]=w^i so w^(e-f)=mu[(e-f)%n]
    mult=mu[(e-f)%n]
    inv=lambda x:pow(x,pr-2,pr)
    S_on_V=0; zero_bad=0; degen=0
    fiber=defaultdict(int) if not want_fibers else defaultdict(list)
    for Sidx,h in cache.items():
        he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
        if (he_r*hf_r1-hf_r*he_r1)%pr!=0: continue
        S_on_V+=1
        if hf_r%pr!=0: gam=(-he_r*inv(hf_r))%pr
        elif hf_r1%pr!=0: gam=(-he_r1*inv(hf_r1))%pr
        else:
            degen+=1; continue
        if gam==0: zero_bad+=1; continue
        if want_fibers: fiber[gam].append(Sidx)
        else: fiber[gam]+=1
    nbad=len(fiber)
    if want_fibers: fibsizes=Counter(len(v) for v in fiber.values())
    else: fibsizes=Counter(fiber.values())
    return dict(n=n,r=r,e=e,f=f,a0=a0,d=d,orbit_size=n//d,
                S_on_V=S_on_V,zero_bad=zero_bad,degen=degen,nbad=nbad,
                fibsizes=fibsizes,K=(1<<r)*comb(n//2,r))

def find_maximizer(n,r,cache,mu,pr):
    a0=r+1; best=None; res=[]
    for e in range(r,n):
        for f in range(r,n):
            if f==e: continue
            a=analyze_line(n,r,e,f,cache,mu,pr,want_fibers=False)
            res.append((a['nbad'],e,f,a['S_on_V'],a['d']))
    res.sort(reverse=True)
    return res

def report(n,r,e,f,cache,mu,pr):
    a=analyze_line(n,r,e,f,cache,mu,pr,want_fibers=True)
    K=a['K']
    print(f"  >>> n={n} r={r} line(x^{e},x^{f})  [e-f={(e-f)}, d=gcd(e-f,n)={a['d']}, orbit n/d={a['orbit_size']}]")
    print(f"      (1) #{{S on V}} (bad subsets) = {a['S_on_V']}")
    print(f"          split: nonzero-gamma subsets={a['S_on_V']-a['zero_bad']-a['degen']}, "
          f"gamma=0 subsets={a['zero_bad']}, fully-degenerate(h_{{f-r}}=h_{{f-r+1}}=0)={a['degen']}")
    print(f"      (2) #bad (distinct nonzero gamma) = {a['nbad']}   K=2^{r}*C({n//2},{r})={K}")
    print(f"          #{{S on V}} <= K ?  {a['S_on_V']} <= {K} : {a['S_on_V']<=K}   "
          f"(#{{S on V}}/K={a['S_on_V']/K:.4f})")
    print(f"          #bad <= #{{S on V}} ? {a['nbad']} <= {a['S_on_V']} : {a['nbad']<=a['S_on_V']}   "
          f"(#bad/K={a['nbad']/K:.4f})")
    print(f"      (3) gamma-fiber size distribution {{fibersize: #gamma}} = {dict(sorted(a['fibsizes'].items()))}")
    print(f"          (orbit size n/d={a['orbit_size']}; if all fibers == n/d, each gamma = one dilation orbit's worth)")
    return a

if __name__=="__main__":
    pr=p
    # CALIBRATION
    print("=== CALIBRATION r=3 (expect #bad=n*C(n/4,2)=96,896 ; O_P=6,28) ===")
    for n in [16,32]:
        w=w_of_order(n,pr); mu=[pow(w,i,pr) for i in range(n)]
        a0=4; mmax=n//2  # e=n/2 => e-r+1 = n/2-2; enough
        cache=build_h_cache(n,a0,mmax,mu,pr)
        a=analyze_line(n,3,n//2,n//2-1,cache,mu,pr,want_fibers=True)
        # O_P = nbad/orbit_size if fibers uniform
        print(f"  n={n}: #{{S on V}}={a['S_on_V']} #bad(nz distinct)={a['nbad']} "
              f"zero-subsets={a['zero_bad']} -> O_P={a['nbad']//a['orbit_size']} (expect {comb(n//4,2)})")

    print("\n=== r=6 MAXIMIZER SEARCH + MEASUREMENT ===")
    for n in [16,32]:
        r=6; a0=7
        w=w_of_order(n,pr); mu=[pow(w,i,pr) for i in range(n)]
        mmax=n-1  # max h index = e-r+1 <= (n-1)-6+1 = n-6 ; n-1 is safe
        print(f"-- building h-cache n={n} a0={a0} (C(n,a0)={comb(n,a0)} subsets, mmax={mmax}) ...", flush=True)
        cache=build_h_cache(n,a0,mmax,mu,pr)
        res=find_maximizer(n,r,cache,mu,pr)
        print(f"   top 6 lines by #bad: {[(b,f'x^{e},x^{ff}') for b,e,ff,sv,d in res[:6]]}")
        bestbad,be,bf,bsv,bd=res[0]
        report(n,r,be,bf,cache,mu,pr)
