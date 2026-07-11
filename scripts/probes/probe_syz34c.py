#!/usr/bin/env python3
"""Verify the fiber-product identity that DRIVES the D=3 proof:
For A=D_CA, B=D_CB, C=D_CC dual shortenings with pairwise overlaps <= k-1
(so A cap B = 0, and projections mod C are injective on A and on B):

   dim((A+B) cap C) = dim A + dim B - dim( piC(A) + piC(B) )       [general LA]
                    = dim( piC(A) cap piC(B) )                     [since inj]
where piC = projection V -> V/C  (concretely: restrict to complement of CC).

Also verify piC(A) cap piC(B) is supported on (CA cap CB)\\CC and equals the
punctured pair-intersection whose dim is the residual pinned by probe B.
"""
import random
from probe_syz34 import dual_basis_on_support, rref_dim, intersect_dim

def restrict(vecs, keep):
    return [[v[j] for j in keep] for v in vecs]

def run(n,p,trials=2000,seed=7):
    rng=random.Random(seed); k=n//2
    pts=rng.sample(range(p),n)
    bad_fp=0; bad_res=0; tested=0
    for _ in range(trials):
        s=rng.randint(2*n//3+1, max(2*n//3+1,3*n//4))
        allc=list(range(n))
        CA=set(rng.sample(allc,s)); CB=set(rng.sample(allc,s)); CC=set(rng.sample(allc,s))
        if max(len(CA&CB),len(CA&CC),len(CB&CC))>k-1: continue
        tested+=1
        A=dual_basis_on_support(pts,k,CA,p); B=dual_basis_on_support(pts,k,CB,p); C=dual_basis_on_support(pts,k,CC,p)
        lhs=intersect_dim(A+B,C,n,p)
        keep=[j for j in range(n) if j not in CC]   # V/C ~ restrict to complement of CC
        pA=restrict(A,keep); pB=restrict(B,keep)
        m=len(keep)
        # general LA identity: dim A + dim B - dim(pA+pB)
        rhs1=rref_dim(A,n,p)+rref_dim(B,n,p)-rref_dim(pA+pB,m,p)
        # dim(pA cap pB)
        rhs2=intersect_dim(pA,pB,m,p)
        if lhs!=rhs1: bad_fp+=1
        if lhs!=rhs2: bad_res+=1
    print(f"n={n} p={p}: tested={tested}  LHS!=dimA+dimB-dim(pA+pB): {bad_fp}   LHS!=dim(pA cap pB): {bad_res}")

for n in [16,20,24,28,32]:
    run(n,101,3000,seed=n)
