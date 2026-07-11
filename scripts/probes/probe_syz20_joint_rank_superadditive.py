#!/usr/bin/env python3
"""SYZ20 arithmetic probe: joint-rank super-additivity corrected LP.

Two parts:
 (A) Verify the MDS-duality dimension fact numerically over GF(p):
     dim {c in C^perp : supp(c) subset U} = max(0, |U| - k)  for RS[n,k] (MDS).
 (B) Compute the corrected degenerate-channel LP optimum using the joint-rank
     constraint (union-based) + the merge cap (pairwise overlap <= k-1 => sunflower
     min union => per-core cost (s - k + 1)), for both the CONTINUOUS relaxation and
     the INTEGER program, and compare to budget B=n and the SYZ7 empirical maxima.
"""
from fractions import Fraction
import itertools, random

# ---------- (A) MDS duality dimension check ----------
def rref_rank(rows, p):
    rows = [r[:] for r in rows]
    m = len(rows);
    if m==0: return 0
    ncol = len(rows[0]); r=0
    for c in range(ncol):
        piv=None
        for i in range(r,m):
            if rows[i][c]%p!=0: piv=i;break
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],p-2,p)
        rows[r]=[(x*inv)%p for x in rows[r]]
        for i in range(m):
            if i!=r and rows[i][c]%p!=0:
                f=rows[i][c]
                rows[i]=[(rows[i][j]-f*rows[r][j])%p for j in range(ncol)]
        r+=1
        if r==m: break
    return r

def check_mds_duality(n,k,p,trials=20):
    # RS[n,k]: eval of deg<k polys at points 0..n-1. Parity check H = Vandermonde rows x^i, i=k..n-1
    xs=list(range(n))
    # dual code C^perp basis: generalized; for RS, dual is GRS. We instead directly build
    # the space {c in F^U : c is a codeword of C^perp} = {c: sum_j c_j x_j^i =0 for i=0..k-1}?
    # C = {(f(x_j)): deg f<k}. c in C^perp iff sum_j c_j f(x_j)=0 for all deg f<k
    #   iff sum_j c_j x_j^i = 0 for i=0..k-1.  So dual defined by k constraints (rows x^i,i<k).
    ok=True
    for _ in range(trials):
        u=random.randint(k, n)  # |U|
        U=random.sample(range(n), u)
        # words supported on U in C^perp: variables c_j for j in U, constraints sum_{j in U} c_j x_j^i=0, i=0..k-1
        # dimension = |U| - rank(constraint matrix over columns U) = |U| - min(|U|,k) generically = |U|-k
        Amat=[[pow(xs[j],i,p) for j in U] for i in range(k)]
        rk=rref_rank(Amat,p)
        dim=len(U)-rk
        expect=max(0,len(U)-k)
        if dim!=expect: ok=False; print("  MISMATCH",u,dim,expect)
    return ok

# ---------- (B) corrected LP ----------
def yield_s(n,s,t):
    if s>=t: return n-s
    if s<=  0: return 0
    if t-s<=0: return 0
    return (n-s)//(t-s)

def core_cost(s,k):   # sunflower min-union incremental cost = s-(k-1)
    return s-(k-1)

def corrected_lp(n,k,t,B):
    # feasible core sizes: s from k+1 .. n-1 ; degenerate needs core supporting codeword => s>=k? need s>=k+1 (nontrivial), and to certify at t need s+? >= t reachable (s<t needs t-s|... yield>0)
    best_cont=Fraction(0); best_int=0; arg_cont=None; arg_int=None
    budget_rank=n-k   # sum of costs <= n-k (|U|<=n-1)
    for s in range(k+1, n):
        y=yield_s(n,s,t)
        if y<=0: continue
        c=core_cost(s,k)
        if c<=0: continue
        # continuous: D = budget_rank / c
        cont=Fraction(y*budget_rank, c)
        if cont>best_cont: best_cont=cont; arg_cont=(s,y,c)
        # integer: D = floor(budget_rank/c)
        D=budget_rank//c
        it=D*y
        if it>best_int: best_int=it; arg_int=(s,y,c,D)
    return best_cont,arg_cont,best_int,arg_int

def johnson(n,k):
    import math
    return 1-math.sqrt(k/n)

print("=== (A) MDS-duality dim(dual codewords supported in U)=max(0,|U|-k) ===")
for (n,k,p) in [(32,16,97),(64,32,131),(16,8,17)]:
    print(f"  RS[{n},{k}] over F_{p}: ", "PASS" if check_mds_duality(n,k,p) else "FAIL")

print("\n=== (B) corrected joint-rank+merge LP vs budget & empirics (n=64,k=32,B=64) ===")
n,k,B=64,32,64
print(f"  Johnson delta ~ {johnson(n,k):.4f}, 1/3=0.3333")
print(f"  {'t':>3} {'delta':>7} {'zone':>10} {'LPcont':>8} {'argC':>14} {'LPint':>6} {'argI':>16} {'budget':>7}")
emp={39:104,40:100,41:72,42:69,43:44,44:42,45:40,46:38,48:17}
for t in [39,40,41,42,43,44,45,46,48]:
    delta=(n-t)/n
    zone="above-1/3" if delta>1/3+1e-9 else ("STRIP" if delta>=johnson(n,k)-1e-9 else "below-J")
    cont,ac,it,ai=corrected_lp(n,k,t,B)
    print(f"  {t:>3} {delta:>7.4f} {zone:>10} {float(cont):>8.1f} {str(ac):>14} {it:>6} {str(ai):>16} {B:>7}   emp={emp.get(t)}")

print("\n=== n=32,k=16,B=32 ===")
n,k,B=32,16,32
for t in [19,20,21,22,23,24]:
    delta=(n-t)/n
    zone="above-1/3" if delta>1/3+1e-9 else ("STRIP" if delta>=johnson(n,k)-1e-9 else "below-J")
    cont,ac,it,ai=corrected_lp(n,k,t,B)
    print(f"  t={t} d={delta:.4f} {zone:>10} LPcont={float(cont):.1f} arg={ac} LPint={it} arg={ai} B={B}")
