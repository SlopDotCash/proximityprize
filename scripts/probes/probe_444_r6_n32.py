"""
r=6 n=32 focused: confirm maximizer (target O_P=185) within small e-f families, then full report.
Caches h once; scans only |e-f| in {1,2,3,4} (n=16 winner had e-f=2). Unbuffered.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter, defaultdict
p=2013265921

def w_of_order(n,pr):
    e=(pr-1)//n
    for c in range(2,4000):
        h=pow(c,e,pr)
        if pow(h,n,pr)==1 and pow(h,n//2,pr)!=1: return h
    raise RuntimeError

def pr(*a): print(*a,flush=True)

def build_cache(n,a0,mmax,mu,P):
    cache={}
    inv_m=[0]+[pow(m,P-2,P) for m in range(1,mmax+1)]
    for Sidx in itertools.combinations(range(n),a0):
        PS=[0]*(mmax+1)
        for i in Sidx:
            z=mu[i]; zi=1
            for j in range(1,mmax+1):
                zi=(zi*z)%P; PS[j]=(PS[j]+zi)%P
        h=[0]*(mmax+1); h[0]=1
        for m in range(1,mmax+1):
            s=0
            for ii in range(1,m+1): s=(s+PS[ii]*h[m-ii])%P
            h[m]=(s*inv_m[m])%P
        cache[Sidx]=h
    return cache

def analyze(n,r,e,f,cache,mu,P,fibers=False):
    i1,i2,i3,i4=e-r,e-r+1,f-r,f-r+1
    d=gcd((e-f)%n,n)
    inv=lambda x:pow(x,P-2,P)
    S_on_V=0; zero_bad=0; degen=0
    fib=defaultdict(list) if fibers else defaultdict(int)
    for Sidx,h in cache.items():
        he_r=h[i1];he_r1=h[i2];hf_r=h[i3];hf_r1=h[i4]
        if (he_r*hf_r1-hf_r*he_r1)%P!=0: continue
        S_on_V+=1
        if hf_r%P!=0: g=(-he_r*inv(hf_r))%P
        elif hf_r1%P!=0: g=(-he_r1*inv(hf_r1))%P
        else: degen+=1; continue
        if g==0: zero_bad+=1; continue
        if fibers: fib[g].append(Sidx)
        else: fib[g]+=1
    nbad=len(fib)
    fs=Counter(len(v) for v in fib.values()) if fibers else Counter(fib.values())
    return dict(S_on_V=S_on_V,zero_bad=zero_bad,degen=degen,nbad=nbad,d=d,
                orbit=n//d,fibsizes=fs,K=(1<<r)*comb(n//2,r))

if __name__=="__main__":
    P=p; n=32; r=6; a0=7; mmax=n-1
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    pr(f"building cache n={n} a0={a0} subsets={comb(n,a0)} ...")
    cache=build_cache(n,a0,mmax,mu,P)
    pr("cache built. scanning |e-f| in {1,2,3,4} ...")
    res=[]
    for e in range(r,n):
        for f in range(r,n):
            if f==e: continue
            if abs(e-f) not in (1,2,3,4) and abs(e-f) not in (n-1,n-2,n-3,n-4): continue
            a=analyze(n,r,e,f,cache,mu,P,fibers=False)
            mult=mu[(e-f)%n]
            # orbit count of distinct nonzero gamma
            res.append((a['nbad'],e,f,a['S_on_V'],a['d']))
    res.sort(reverse=True)
    pr("top 8 by #bad:")
    for b,e,f,sv,d in res[:8]:
        pr(f"   line(x^{e},x^{f}) d={d}: #bad={b} S_on_V={sv} O_P={b//(n//d)}")
    # full report on the winner
    b,be,bf,bsv,bd=res[0]
    a=analyze(n,r,be,bf,cache,mu,P,fibers=True)
    K=a['K']
    pr(f"\n>>> MAXIMIZER n={n} r={r} line(x^{be},x^{bf}) e-f={be-bf} d={a['d']} orbit={a['orbit']}")
    pr(f"  (1) #{{S on V}} = {a['S_on_V']}  (nonzero-g={a['S_on_V']-a['zero_bad']-a['degen']}, g=0 subsets={a['zero_bad']}, degenerate={a['degen']})")
    pr(f"  (2) #bad(distinct nz g)={a['nbad']}  K={K}  S_on_V<=K:{a['S_on_V']<=K} ({a['S_on_V']/K:.4f})  bad<=S_on_V:{a['nbad']<=a['S_on_V']}  bad/K={a['nbad']/K:.4f}")
    pr(f"  (3) gamma-fiber sizes {{size:#gamma}} = {dict(sorted(a['fibsizes'].items()))}  (orbit n/d={a['orbit']})")
    pr(f"      O_P = #bad/orbit = {a['nbad']//a['orbit']}")
