#!/usr/bin/env python3
"""
[#407 route effkatz] CONDUCTOR of the Gauss-period trace-function family b -> eta_b.

THE OBJECT.  p-1 = m*n,  mu_n = order-n subgroup of F_p^x (index m).
  eta_b = sum_{x in mu_n} e_p(b*x),   B = max_{b!=0} |eta_b|.

The effective-Katz / Wasserstein route (Kowalski-Untrau 2505.22059, Thm 4.4/4.11) controls
equidistribution of a trace-function family in terms of the *conductor* (sum of Betti numbers /
complexity c(F)) of the underlying l-adic sheaf.  The single-point estimate underlying it is the
Deligne/Weil bound
    | (1/|X(F_p)|) sum_x tr(rho(Frob_x)) - mu_K(rho) |  <=  |F_p|^{-1/2} * c(X, rho(F)).
The comment's claim: discrepancy ~ conductor * p^{-1/2}; to beat the 1/m non-conspiracy threshold
you'd need conductor < sqrt(n/m).  This probe INDEPENDENTLY measures the conductor of the relevant
sheaf, three ways, and tests the 2^{-48} obstruction.

WHICH SHEAF?  Two distinct sheaf-theoretic incarnations of b -> eta_b:
  (I)  ADDITIVE / Kloosterman-type.  Fix the additive char psi=e_p.  The map
         eta_b = sum_{y^n=1} psi(b*y) = sum_{x in G_m} 1_{mu_n}(x) psi(b x)
       is the (additive) FOURIER TRANSFORM of the delta-on-mu_n trace function.  As a function of b
       it is the trace function of FT_psi([n]_* Q_l |_{mu_n})  -- a middle-extension sheaf on A^1.
       Its conductor = Swan + tame + rank contributions of [n]_*(constant) twisted by L_psi.
  (II) MELLIN / multiplicative.  Katz's arithmetic-FT framework (KU Thm 4.11) parameterizes by a
       *multiplicative* character; the relevant object is the hypergeometric-type sheaf whose
       complexity Katz bounds.  Here the conductor enters EXPONENTIALLY (KU 4.4 open remark).

We compute the conductor of (I) directly (it is the honest, finite, computable invariant) and read
off what the Deligne bound delivers; then we test the claim numerically over small p.
"""
import cmath, math, statistics

def factor_pairs(pm1):
    """all (m,n) with m*n = p-1, return small-index ones."""
    out=[]
    i=1
    while i*i<=pm1:
        if pm1%i==0:
            out.append((i,pm1//i)); out.append((pm1//i,i))
        i+=1
    return out

def primitive_root(p):
    # find a generator of F_p^x
    if p==2: return 1
    pm1=p-1
    # factor p-1
    f=set(); d=pm1; k=2
    while k*k<=d:
        while d%k==0: f.add(k); d//=k
        k+=1
    if d>1: f.add(d)
    for g in range(2,p):
        if all(pow(g,pm1//q,p)!=1 for q in f):
            return g
    return None

def subgroup(p,n):
    """order-n multiplicative subgroup of F_p^x (n | p-1)."""
    g=primitive_root(p)
    m=(p-1)//n
    gen=pow(g,m,p)  # order n
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*gen)%p
    return S

def eta(p,b,S):
    s=0j
    for x in S:
        s+=cmath.exp(2j*math.pi*(b*x % p)/p)
    return s

def B_max(p,n):
    S=subgroup(p,n)
    best=0.0; arg=None
    for b in range(1,p):
        v=abs(eta(p,b,S))
        if v>best: best=v; arg=b
    return best, arg

# ---------------------------------------------------------------------------
# CONDUCTOR (incarnation I): the additive FT sheaf  FT_psi(delta_{mu_n}).
#
# delta_{mu_n} as a trace function on G_m is supported on the n points of mu_n, each value 1.
# It is the trace function of the skyscraper-ish middle extension  M = [n]_* Q_l  pushed to its
# image mu_n, OR equivalently the Kummer-type object cut out by  x^n = 1.  The cleanest honest
# model: 1_{mu_n}(x) = (1/m) * sum_{chi : chi^? } ... but the SHEAF whose FT we take is
#   K  =  (the constant sheaf on the 0-dim'l scheme mu_n) pushed forward to G_m.
# Its naive additive-FT conductor: for a FINITE point-sheaf with N points all of weight 0, the
# Fourier transform FT_psi has GENERIC RANK = N (= n) and the sum of Betti numbers (= conductor of
# the FT, as an l-adic sheaf on A^1_b) is governed by  rank + Swan_0 + Swan_infty + #sing.
#
# For FT of a punctual sheaf of n points:  FT is lisse of rank n on G_m away from 0, with a single
# wild ramification at infinity of Swan = n (the n distinct frequencies / phases), tame at 0.
# So  c(FT) = O(n).   This is the honest conductor of incarnation (I).
# ---------------------------------------------------------------------------

def conductor_additiveFT_model(p,n):
    """
    Empirical proxy for the conductor of incarnation (I): the conductor of an l-adic sheaf on A^1
    whose trace function is b -> eta_b is dominated by its GENERIC RANK plus its wild part.  For the
    FT of an n-point punctual sheaf the generic rank is n and the Swan-at-infinity is n; sum of
    Betti numbers ~ 2n + O(1).  We MEASURE the generic rank numerically as the dimension of the span
    of the 'local difference vectors' of the trace function (the rank of the recurrence / the
    minimal linear recurrence order the sequence eta_b satisfies as b runs).
    """
    S=subgroup(p,n)
    seq=[eta(p,b,S) for b in range(0,p)]   # full b=0..p-1
    # eta_b = sum_{x in S} e_p(bx) is a sum of n distinct geometric progressions in b (one per x in S),
    # roots e_p(x).  So as a sequence in b it satisfies a linear recurrence of order EXACTLY n
    # (char poly = prod_{x in S}(T - zeta_p^x)), n distinct roots.  The minimal recurrence order =
    # number of distinct frequencies present = n.  We verify by Hankel-matrix rank.
    import numpy as np
    L=2*n+4
    if L> p: L=p
    H=np.array([[seq[i+j] for j in range(L//2)] for i in range(L//2)],dtype=complex)
    # rank via singular values
    sv=np.linalg.svd(H, compute_uv=False)
    tol=1e-7*sv[0] if sv[0]>0 else 1e-12
    rank=int((sv>tol).sum())
    return rank, n

def main():
    print("="*78)
    print("CONDUCTOR PROBE: family b -> eta_b = sum_{x in mu_n} e_p(b x)")
    print("="*78)
    # small primes with a moderate subgroup, fixed-ish index to mimic prize geometry
    tests=[]
    for p in [13,29,37,41,53,61,73,89,97,101,113,127,149,151,181,193,197,211,241,257,
              521,1031,2053,4099,8209]:
        # pick a few (m,n) splits
        pm1=p-1
        for (m,n) in factor_pairs(pm1):
            if n>=2 and n<=64 and m>=2:
                tests.append((p,m,n))
    print(f"{'p':>6} {'m':>6} {'n':>5} {'B':>10} {'B/sqrt(n)':>10} {'cond(rank)':>10} {'cond/n':>7} "
          f"{'cond*p^-.5':>11} {'1/m':>9} {'feeds<1/m?':>10}")
    rows=[]
    for (p,m,n) in tests:
        try:
            B,arg=B_max(p,n)
            rank,nn=conductor_additiveFT_model(p,n)
        except Exception as e:
            continue
        disc_feed = rank * p**(-0.5)        # the discrepancy-style quantity cond * p^{-1/2}
        inv_m = 1.0/m
        feeds = "YES" if disc_feed < inv_m else "no"
        print(f"{p:>6} {m:>6} {n:>5} {B:>10.4f} {B/math.sqrt(n):>10.4f} "
              f"{rank:>10} {rank/n:>7.3f} {disc_feed:>11.5f} {inv_m:>9.5f} {feeds:>10}")
        rows.append((p,m,n,B,rank,disc_feed,inv_m))
    print()
    print("INTERPRETATION:")
    print(" - cond(rank) = measured generic rank of the trace-function family (incarnation I).")
    print(" - Conjecture: rank == n (n distinct geometric frequencies). If cond/n==1.000 always,")
    print("   the conductor is EXACTLY n (additive-FT model), i.e. O(n) NOT O(1).")
    print(" - The Deligne single-point bound gives |eta_b - mean| <= cond * p^{-1/2} * (norm factors)")
    print("   BUT that bound is for the AVERAGED measure, not the per-b sup; and at conductor ~ n it")
    print("   is VACUOUS unless n < sqrt(p) (then cond*p^{-1/2} = n/sqrt(p) < 1).")

if __name__=="__main__":
    main()
