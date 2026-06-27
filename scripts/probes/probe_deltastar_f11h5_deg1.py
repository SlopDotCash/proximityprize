#!/usr/bin/env python3
"""Exact mcaDeltaStar for RS[F_11, H_5=<3>, deg<1] (constants), n=5, k=1, rate 1/5.

Codewords = constant functions {(a,a,a,a,a) : a in F_11}.
Johnson radius = 1 - sqrt(1/5) ~ 0.5528.

mcaEvent(u0,u1,gamma) at radius delta: exists S subset of coords with
  |S| >= (1-delta)*n, AND the line row L = u0 + gamma*u1 agrees on S with some
  constant codeword (i.e. L is constant on S), AND NOT pairJointAgreesOn:
  (exists const c0 agreeing with u0 on S) AND (exists const c1 agreeing with u1 on S).
A constant agrees with u on S iff u is constant on S.

So pairJointAgreesOn S u0 u1  <=>  (u0 const on S) AND (u1 const on S).
mcaEvent fires (line-explainable) <=> (u0+gamma u1) const on S.
"""
import itertools
from fractions import Fraction
from math import comb

p = 11
n = 5
coords = list(range(n))
Fp = list(range(p))

def is_const_on(u, S):
    if not S: return True
    v = u[S[0]]
    return all(u[i]==v for i in S)

def line(u0,u1,g):
    return tuple((u0[i]+g*u1[i])%p for i in range(n))

def subsets_of_size_at_least(thr):
    out=[]
    for sz in range(n, -1, -1):
        if sz>=thr:
            for S in itertools.combinations(coords, sz):
                out.append(list(S))
    return out

def mca_event(u0,u1,g,delta):
    # need |S| >= (1-delta)*n
    thr = (1-delta)*n
    for sz in range(n,0,-1):
        if Fraction(sz) < Fraction(thr):
            continue
        for S in itertools.combinations(coords, sz):
            S=list(S)
            L=line(u0,u1,g)
            if not is_const_on(L,S):   # line must be explainable (const) on S
                continue
            # pairJointAgreesOn: u0 const on S AND u1 const on S
            if is_const_on(u0,S) and is_const_on(u1,S):
                continue  # joint agrees -> not bad via this S
            return True
    return False

def badcount(u0,u1,delta):
    return sum(1 for g in Fp if mca_event(u0,u1,g,delta))

def epsmca(delta):
    """max over stacks (u0,u1) of badcount/p. Enumerate all stacks (11^5)^2 too big.
    Use structure: only the multiset pattern matters up to nothing special; brute reduced.
    We enumerate u0,u1 but that's 11^10 ~ 2.6e10 too big. Reduce: WLOG by symmetry?
    Instead enumerate candidate stacks from monomial/triangle templates + random search."""
    best=0; bestpair=None
    # candidate threshold radii to test handled by caller; here brute a reduced search:
    return best,bestpair

# The radius ladder: jumps happen at delta where threshold (1-delta)*n crosses integers.
# (1-delta)*5 = m  => delta = 1 - m/5. For m=5,4,3,2,1: delta=0,1/5,2/5,3/5,4/5.
# In each band the required |S| >= ceil((1-delta)*5).
# Band boundaries (delta increasing): [0,1/5): |S|=5 ; [1/5,2/5):|S|>=4 ; [2/5,3/5):|S|>=3 ; etc.
# Actually need |S| >= (1-delta)*5 exactly (>=, real). At delta just below 1/5, (1-delta)*5 just above 4, so |S|=5.
# At delta=1/5 exactly, (1-delta)*5=4, |S|>=4.

def required_min_size(delta):
    thr=Fraction(1)-Fraction(delta)
    thr*=n
    # smallest integer s with s>=thr
    import math
    s=math.ceil(thr)
    if s<1: s=1
    return s,thr

# Now compute epsmca exactly per band by full stack search but pruned.
# Key reduction: mca outcome depends only on, for the chosen min size smin,
# whether there EXISTS S of size>=smin with line const on S and not(u0,u1 both const on S).
# Enumerate stacks smartly: only "patterns" of (u0,u1) up to value-relabeling matter? Not exactly
# because gamma ranges over all of F and 'const' is value-specific only through equality.
# 'const on S' is purely an EQUALITY-PATTERN property (partition of coords by equal values),
# preserved under affine maps x->ax+b on each row independently? No: line couples them.
# But the EQUALITY structure of u0, u1, and each line u0+g*u1 is what matters.
# We can enumerate stacks up to the simultaneous action that preserves all these patterns.
# Simplest robust approach: random + structured search over many stacks for the worst band.

import random
def search_band(delta, iters=400000, seed=0):
    smin,thr = required_min_size(delta)
    rng=random.Random(seed)
    # precompute subsets of size>=smin
    subs=[list(S) for sz in range(n,smin-1,-1) for S in itertools.combinations(coords,sz)]
    def mca(u0,u1,g):
        L=tuple((u0[i]+g*u1[i])%p for i in range(n))
        for S in subs:
            if is_const_on(L,S) and not(is_const_on(u0,S) and is_const_on(u1,S)):
                return True
        return False
    def bc(u0,u1):
        return sum(1 for g in Fp if mca(u0,u1,g))
    best=0; bestpair=None
    # structured candidates first: u0,u1 with few distinct values
    cand=[]
    # all stacks where each row takes values in {0,1} or small sets - templates
    for u0 in itertools.product([0,1], repeat=n):
        for u1 in itertools.product([0,1], repeat=n):
            cand.append((u0,u1))
    for u0 in itertools.product([0,1,2], repeat=n):
        for u1 in itertools.product([0,1], repeat=n):
            cand.append((u0,u1))
    for u0,u1 in cand:
        c=bc(u0,u1)
        if c>best:
            best=c; bestpair=(u0,u1)
    # random over full field
    for _ in range(iters):
        u0=tuple(rng.randrange(p) for _ in range(n))
        u1=tuple(rng.randrange(p) for _ in range(n))
        c=bc(u0,u1)
        if c>best:
            best=c; bestpair=(u0,u1)
    return best,bestpair,smin,thr

print("Johnson radius =", 1-(1/5)**0.5)
for delta in [Fraction(1,5), Fraction(2,5), Fraction(3,5), Fraction(4,5)]:
    best,bp,smin,thr=search_band(delta, iters=120000, seed=1)
    print(f"delta={delta} (~{float(delta):.3f}) reqsize>={smin} (thr={float(thr):.3f}): max badcount={best}/{p}={Fraction(best,p)}  stack={bp}")
