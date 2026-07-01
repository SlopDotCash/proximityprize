"""
Reconcile Schur-V count vs GENUINE bad-subset count (interpolation) for the r=6 maximizers.
The genuine "#{S on V}" the task wants = # genuinely bad (r+1)-subsets = interpolation 'bad' event.
We classify each subset by BOTH definitions and report:
  - Schur-V count (h identity = 0)
  - genuine-bad count (interpolation: consistent single gamma over coords k..a0-1, non-degenerate)
  - and the gamma distribution from the GENUINE definition.
Run for n=16 maximizer (x^12,x^10) [d=2] and n=32 maximizer (x^20,x^18) [d=2] and the chain-break
line x^20,x^16 [d=4]. For n=32 this is heavy (interpolation on 3.4M) -> n=16 full, n=32 we compute
genuine count by the h-logic that EXACTLY matches interpolation (validated on n=16).

KEY: interpolation 'bad' = exists single gamma s.t. for all j in [k,a0): c0[j]+gamma c1[j]=0, with
NOT all (c0[j],c1[j])=0 (nd). Equivalent h-form: the bad event is the SUBVARIETY of V where the
two vectors (h_{e-r},h_{e-r+1}) and (h_{f-r},h_{f-r+1}) are parallel AS THE GAMMA-PINNING, EXCLUDING
the fully-zero degenerate locus. We compare counts.
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
def genuine_bad(pts,e,f,k,a0,P):
    """return (is_bad, gamma or None). matches probe_444_antipodal definition exactly."""
    c0=interp_coeffs(pts,[pow(t,e,P) for t in pts],P)
    c1=interp_coeffs(pts,[pow(t,f,P) for t in pts],P)
    if c0 is None or c1 is None: return (False,None)
    gam=None; nd=False
    for j in range(k,a0):
        x0=c0[j];x1=c1[j]
        if x0 or x1: nd=True
        if x1==0:
            if x0: return (False,None)
        else:
            g=(-x0*pow(x1,P-2,P))%P
            if gam is None: gam=g
            elif gam!=g: return (False,None)
    if not nd: return (False,None)
    return (True, gam if gam is not None else 0)

def run_interp(n,r,e,f,P):
    a0=r+1;k=r-1
    w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
    son=0; fib=defaultdict(int); zero=0
    for Sidx in itertools.combinations(range(n),a0):
        pts=[mu[i] for i in Sidx]
        ok,g=genuine_bad(pts,e,f,k,a0,P)
        if not ok: continue
        son+=1
        if g==0: zero+=1
        else: fib[g]+=1
    K=(1<<r)*comb(n//2,r); d=gcd((e-f)%n,n)
    fs=Counter(fib.values())
    pr(f"  GENUINE(interp) n={n} line(x^{e},x^{f}) d={d}: #{{S genuinely bad}}={son} "
       f"(gamma=0 subsets={zero}, nonzero-gamma subsets={son-zero})")
    pr(f"     #bad(distinct nz gamma)={len(fib)}  K={K}  S_bad<=K:{son<=K}({son/K:.4f})  "
       f"O_P={len(fib)//(n//d)}")
    pr(f"     genuine fiber sizes={dict(sorted(fs.items()))}")
    return son,len(fib),K

if __name__=="__main__":
    which=sys.argv[1] if len(sys.argv)>1 else "16"
    if which=="16":
        pr("=== n=16 GENUINE counts ===")
        run_interp(16,6,12,10,p)   # maximizer
    elif which=="32max":
        pr("=== n=32 GENUINE count, maximizer x^20,x^18 ===")
        run_interp(32,6,20,18,p)
    elif which=="32break":
        pr("=== n=32 GENUINE count, chain-break line x^20,x^16 ===")
        run_interp(32,6,20,16,p)
