#!/usr/bin/env python3
"""
#407 NOVEL ROUTE candidate: BOOTSTRAP / self-improvement via multiplicative structure of LEVEL SETS.

Mechanism to test: the "large spectral set" L_lam = {b in F_p^* : |eta_b| >= lam}. The house B is the
largest lam with L_lam nonempty. KEY structural facts we can exploit:
  (i)  eta_{b} for b in same mu_n-coset are EQUAL (coset invariance, proven in-tree). So |eta_b| is a
       function on the COSET GROUP Q = F_p^*/mu_n ~ Z/m. L_lam is a union of cosets <=> a subset S of Z/m.
  (ii) Parseval: sum_{b} |eta_b|^2 = n(p-1) => sum over cosets |eta|^2 = n*m*... ; #cosets with |eta|>=lam
       is <= n*m / lam^2 (Markov). So |S_lam| <= n*m/lam^2 in Z/m.
  (iii) The BOOTSTRAP HOPE (Bourgain-Chang style): if the spectral large-set S_lam in Z/m had small
       SUMSET/doubling or could be "amplified" by the multiplicative action, a sum-product / 
       Balog-Szemeredi-Gowers argument would force lam small. 

WHAT WE ACTUALLY MEASURE (the honest test): does the large-spectral set S_lam carry ARITHMETIC structure
in Z/m (the coset group) that a self-improvement could bite on? Specifically:
  (A) the DOUBLING |S+S|/|S| of the top level set (in Z/m additive),
  (B) the multiplicative energy of S under the natural Z/m action,
  (C) whether the top-eigenvalue cosets cluster (small diameter) or spread (random-like).
A self-improvement route is VIABLE only if S_lam is STRUCTURED (small doubling). If S_lam looks random
(doubling ~ |S|, energy ~ random), there is NO arithmetic handle => the bootstrap CANNOT start.
"""
import math, numpy as np

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def odd_part(x):
    while x%2==0: x//=2
    return x
def primitive_root(p):
    phi=p-1;facs=[];m=phi;d=2
    while d*d<=m:
        if m%d==0:
            facs.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: facs.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError
def find_prime(n,beta,used,pmax):
    target=int(round(n**beta)); p=target-(target%n)+1
    for _ in range(2000000):
        if p>pmax: return None
        if p>3 and is_prime(p) and odd_part((p-1)//n)>1 and p not in used:
            used.add(p); return p
        p+=n
    return None

def coset_periods(p,n):
    """eta over a transversal of cosets, indexed by j in Z/m where coset rep = g^j. Returns |eta|^2 / n array length m."""
    g=primitive_root(p); eta_gen=pow(g,(p-1)//n,p)
    xs=np.array([pow(eta_gen,i,p) for i in range(n)],dtype=np.int64)
    m=(p-1)//n; twp=2.0*math.pi/p
    out=np.empty(m,dtype=np.float64)
    # coset rep j -> b = g^j. compute incrementally to save pow.
    CH=max(1,6_000_000//n)
    gpow=1
    j=0
    while j<m:
        mlen=min(CH,m-j)
        reps=np.empty(mlen,dtype=np.int64); c=gpow
        for i in range(mlen):
            reps[i]=c; c=c*g%p
        ang=((reps[:,None]*xs[None,:])%p).astype(np.float64)*twp
        S2=np.cos(ang).sum(1)**2+np.sin(ang).sum(1)**2
        out[j:j+mlen]=S2
        gpow=c; j+=mlen
    return out/n, m

def doubling(S, m):
    """|S+S|/|S| in Z/m, S a set of residues."""
    Sset=set(int(x) for x in S)
    if len(Sset)==0: return float('nan')
    sums=set()
    Sl=list(Sset)
    for a in Sl:
        for b in Sl:
            sums.add((a+b)%m)
    return len(sums)/len(Sset)

def main():
    print("="*100, flush=True)
    print(" #407 SELF-IMPROVEMENT VIABILITY: is the top spectral level set STRUCTURED or RANDOM?", flush=True)
    print("="*100, flush=True)
    used=set(); PMAX=12_000_000
    print(f"\n{'n':>4}{'beta':>5}{'p':>10}{'m':>8}{'B/sqn':>7}{'top-k':>6}{'|S+S|/|S|':>10}"
          f"{'rand-dbl':>9}{'ratio':>7}{'verdict':>10}", flush=True)
    for mu in (5,6):
        n=1<<mu
        for beta in (3.5,4.0):
            p=find_prime(n,beta,used,PMAX)
            if p is None: 
                print(f"{n:>4}{beta:>5.1f}  no prime", flush=True); continue
            v2,m=coset_periods(p,n)   # |eta|^2/n per coset
            B=math.sqrt(v2.max()*n)
            # top level set: take cosets with |eta|^2/n in top tier (>= mean of top sqrt(m) say, or threshold)
            order=np.argsort(v2)[::-1]
            for frac_k in (max(8,int(math.sqrt(m))),):
                topidx=order[:frac_k].astype(np.int64)  # the j-indices (in Z/m) of the largest periods
                dbl=doubling(topidx,m)
                # random doubling for a set of size k in Z/m: expected |S+S| ~ m(1-exp(-k^2/(2m))) roughly; 
                # for k<<sqrt(m), ~ k(k+1)/2 distinct (all sums distinct) => dbl ~ (k+1)/2
                k=len(set(int(x) for x in topidx))
                # expected distinct sums (birthday) in Z/m
                num_pairs=k*(k+1)//2
                rand_distinct=m*(1-math.exp(-num_pairs/m))
                rand_dbl=rand_distinct/k
                ratio=dbl/rand_dbl
                verdict = "RANDOM" if ratio>0.7 else "STRUCT!"
                print(f"{n:>4}{beta:>5.1f}{p:>10}{m:>8}{B/math.sqrt(n):>7.2f}{k:>6}{dbl:>10.2f}"
                      f"{rand_dbl:>9.2f}{ratio:>7.2f}{verdict:>10}", flush=True)

if __name__=="__main__":
    main()
