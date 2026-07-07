"""
probe_444_angleC_minpoly.py -- Angle C: bound O_P by the DEGREE of the polynomial whose roots
are the bad-gamma coset reps J=gamma^{n/d}.

Strategy: the bad gammas are exactly the gamma for which the variety
   V_gamma = { S subset mu_n, |S|=r+1 : h_{e-r}(S) + gamma h_{f-r}(S) = 0 }
is nonempty AND S also lies on V (the det locus).  But on the det locus, h_{e-r}+gamma h_{f-r}=0
is EQUIVALENT to gamma being THE pinned scalar.  So {bad gamma} = image of V under S->gamma.

To get a DEGREE bound on #distinct gamma we use the RESULTANT / elimination idea:
  Consider the two symmetric functions A(S)=h_{e-r}(S), B(S)=h_{f-r}(S) as polynomials in the
  power-sums p_1..p_? (Newton).  gamma=-A/B.  The number of distinct gamma is bounded by the
  number of distinct (A:B) in P^1, which (for a generic 1-param family) is the degree of the
  rational map.

CONCRETE TEST we CAN do exactly: the gamma^{n/d} values are roots of a unique monic poly Q(T)
over F_p of degree O_P.  We compute O_P and compare to a sequence of a-priori CRUDE bounds:
   B1 = C(n/2, r)               (the per-CONTEXT K/2^r)
   B2 = C(n/2, r-1)             (one lower)
   B3 = 2^r * C(n/2,r) * d / n  = K*d/n  (the target)
   B4 = (e-r)+(f-r) choose ...  degree-based
We MAINLY want: is O_P <= K*d/n with comfortable slack for ALL admissible lines (not just the
maximizer)?  So scan EVERY admissible line (e,f) with e-r,f-r>=0, e!=f, e,f in a sensible range
and report max O_P / (K*d/n).  If max ratio < 1 across a broad scan AND shrinks in n, that is
strong evidence (still not a proof) and identifies the worst line.
"""
import sys
from math import comb, gcd, factorial
from itertools import combinations
from collections import defaultdict

P=2013265921

def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError

def all_h(n,p=P):
    """Precompute, for every (r+1)-subset, the full h-vector? too big. Instead given r, line, stream."""
    pass

def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def scan_lines(n,r,p=P, emax=None):
    """For fixed (n,r), enumerate all (r+1)-subsets ONCE, precompute h-vector up to n, then for
       each admissible line (e,f) compute O_P from the cached h-values.  Returns dict line->O_P."""
    w=gen(n,p); a0=r+1
    Hmax=n  # need indices e-r,f-r up to ~ n
    subs=list(combinations(range(n),a0))
    # cache H[m] for m=0..Hmax for each subset
    Hcache=[]
    for Sidx in subs:
        xs=[pow(w,i,p) for i in Sidx]
        Hcache.append(hpow(xs,Hmax,p))
    results={}
    # admissible: e-r>=0, f-r>=0, e!=f, and e,f distinct exps; codeword deg k=r-1 so e,f are the
    # monomial witness exponents. Keep e,f in [r, n-1] (mod-n exponents on mu_n), e>f wlog? gamma
    # weight e-f; consider all unordered? gamma differs for (e,f) vs (f,e) -> separate. We scan e in
    # [r, ...], f in [r, ...] e!=f. To bound runtime, cap e,f <= n + r.
    Erange=range(r, n)        # e-r in [0,n-r)
    for e in Erange:
        for f in Erange:
            if e==f: continue
            er,fr,er1,fr1=e-r,f-r,e-r+1,f-r+1
            if er1>Hmax or fr1>Hmax: continue
            d=gcd((e-f)%n,n); nd=n//d
            cosets=set()
            for H in Hcache:
                her,her1,hfr,hfr1=H[er],H[er1],H[fr],H[fr1]
                if (her*hfr1-hfr*her1)%p!=0: continue
                if hfr==0: continue
                g=(-her*pow(hfr,p-2,p))%p
                if g==0: continue
                cosets.add(pow(g,nd,p))
            results[(e,f)]=(len(cosets),d)
    return results

if __name__=="__main__":
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1:
        todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        K=(1<<r)*comb(n//2,r)
        res=scan_lines(n,r)
        # find max O_P and max ratio O_P/(K*d/n)
        best=max(res.items(), key=lambda kv: kv[1][0])
        worst_ratio=max(((op/(K*d/n)), (e,f), op, d) for (e,f),(op,d) in res.items())
        (rr,ef,op,d)=worst_ratio
        print(f"r={r} n={n} K={K}: maxO_P={best[1][0]} at line {best[0]} (d={best[1][1]}); "
              f"WORST O_P/(Kd/n)={rr:.3f} at line {ef} O_P={op} d={d} Kd/n={K*d/n:.1f}; "
              f"#lines scanned={len(res)}; ALL O_P<=Kd/n? {all(op2<=K*d2/n for (op2,d2) in res.values())}")
