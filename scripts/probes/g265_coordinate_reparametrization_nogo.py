#!/usr/bin/env python3
"""G265: quotient coordinate reparametrization is simultaneous, so it cannot reverse CORE.

G258 relabelled the weighted relation profile W while holding the adjacent-rank row R fixed.
That is a valid countermodel to label-free data, but it is not a physical change of primitive-root
coordinates: changing a primitive root relabels BOTH W and R by the same quotient unit.

This probe computes the characteristic-p objects exactly and proves experimentally, with hard
assertions, that:
  * every primitive-root change g -> g^a gives w_a(j)=w(aj), R_a(j)=R(aj);
  * centeredCov(w_a,R_a)=centeredCov(w,R) for every primitive exponent tested;
  * in G258's flagship cell, the one-sided relabel reverses both ranks, while the corresponding
    simultaneous relabel restores the exact base covariances;
  * the affine stabilizer of the subgroup is {(h,0): h in G}, hence acts trivially on F_p^*/G.

Exact integer arithmetic for every covariance. FFT is not used.
"""
from __future__ import annotations
import math


def prime_factors(n: int) -> list[int]:
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out


def primitive_root(p: int) -> int:
    fs=prime_factors(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError("primitive root not found")


def subgroup(p: int,n: int,g: int) -> list[int]:
    z=pow(g,(p-1)//n,p); G=[]; x=1
    for _ in range(n): G.append(x); x=x*z%p
    assert x==1 and len(set(G))==n
    return G


def subset_hists(G: list[int],p: int,rmax: int) -> list[list[int]]:
    dp=[[0]*p for _ in range(rmax+1)]; dp[0][0]=1
    for used,x in enumerate(G,1):
        for r in range(min(used,rmax),0,-1):
            prev=dp[r-1]; cur=dp[r]
            for t,v in enumerate(prev):
                if v: cur[(t+x)%p]+=v
    for r,row in enumerate(dp): assert sum(row)==math.comb(len(G),r)
    return dp


def exact_corr(a: list[int],b: list[int]) -> list[int]:
    p=len(a); out=[0]*p
    nzb=[(j,v) for j,v in enumerate(b) if v]
    for i,u in enumerate(a):
        if u:
            for j,v in nzb: out[(i-j)%p]+=u*v
    assert sum(out)==sum(a)*sum(b)
    return out


def field_profiles(n: int,p: int,ranks=(5,6)):
    g=primitive_root(p); G=subgroup(p,n,g); m=(p-1)//n
    W=[0]*p
    for y in G:
        for z in G: W[(2*y-z)%p]+=1
    dp=subset_hists(G,p,max(ranks))
    Rs={r: exact_corr(dp[r],dp[r-1]) for r in ranks}
    return g,G,m,W,Rs


def quotient_profile(field_row: list[int],g: int,m: int,p: int) -> list[int]:
    return [field_row[pow(g,j,p)] for j in range(m)]


def mul_relabel(row: list[int],a: int) -> list[int]:
    m=len(row); return [row[(a*j)%m] for j in range(m)]


def centered_cov(w: list[int],r: list[int]) -> int:
    m=len(w)
    return m*sum(x*y for x,y in zip(w,r))-sum(w)*sum(r)


def primitive_exponents(p: int) -> list[int]:
    return [a for a in range(1,p-1) if math.gcd(a,p-1)==1]


def check_cell(n: int,p: int,all_exponents: bool=True):
    g,G,m,W,Rs=field_profiles(n,p)
    w=quotient_profile(W,g,m,p)
    rr={r: quotient_profile(Rs[r],g,m,p) for r in Rs}
    base={r:centered_cov(w,rr[r]) for r in rr}
    exps=primitive_exponents(p)
    if not all_exponents and len(exps)>160:
        exps=exps[:80]+exps[-80:]
    for a in exps:
        ga=pow(g,a,p)
        wa=quotient_profile(W,ga,m,p)
        assert wa==mul_relabel(w,a%m)
        for r in rr:
            ra=quotient_profile(Rs[r],ga,m,p)
            assert ra==mul_relabel(rr[r],a%m)
            assert centered_cov(wa,ra)==base[r]
    # Affine subgroup stabilizer theorem, checked from its exact two-step proof.
    # sum(G)=0, so aG+b=G implies n*b=0, hence b=0; then aG=G iff a in G.
    assert sum(G)%p==0 and n%p!=0
    for a in range(1,p):
        preserves=(set((a*x)%p for x in G)==set(G))
        assert preserves==(a in set(G))
    print(f"n={n} p={p} m={m}: primitive-coordinate choices checked={len(exps)}; "
          f"all simultaneous covariances invariant; affine stabilizer={n}, quotient action trivial; "
          f"base=({base[5]:+d},{base[6]:+d})")
    return g,m,w,rr,base


def main():
    print("# G265 coordinate reparametrization no-go")
    g,m,w,rr,base=check_cell(16,1297,True)
    assert m==81 and base=={5:1261081,6:3691265}

    # G258 uses w'(x)=w(53*x), called the a=26 relabel because 26^{-1}=53 mod 81.
    exponent=53
    moved_w=mul_relabel(w,exponent)
    one_sided={r:centered_cov(moved_w,rr[r]) for r in rr}
    moved_r={r:mul_relabel(rr[r],exponent) for r in rr}
    simultaneous={r:centered_cov(moved_w,moved_r[r]) for r in rr}
    assert one_sided=={5:-346283,6:-1161769}
    assert simultaneous==base
    # Direct primitive-root recomputation is exactly the simultaneous relabel.
    gp=pow(g,exponent,1297)
    _,_,_,Wfield,Rs=field_profiles(16,1297)
    assert quotient_profile(Wfield,gp,m,1297)==moved_w
    for r in rr: assert quotient_profile(Rs[r],gp,m,1297)==moved_r[r]
    print("flagship (16,1297,m=81), root exponent 53:")
    print(f"  one-sided W relabel vs fixed R: ({one_sided[5]:+d},{one_sided[6]:+d})  [G258 reversal]")
    print(f"  physical coordinate change, W and R together: ({simultaneous[5]:+d},{simultaneous[6]:+d}) = base")

    for cell in [(8,1801),(32,641),(64,3329),(32,3617)]:
        check_cell(*cell,all_exponents=False)

    print("G265 PROBE PASS: primitive-root/unit coordinate freedom is diagonal on (W,R),")
    print("so it preserves the centered covariance exactly. One-sided relabeling is a")
    print("label-free countermodel, not a physical symmetry of the fixed sponsor pair.")


if __name__=="__main__": main()
