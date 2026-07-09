#!/usr/bin/env python3
"""
probe_444_cdep_np.py  (#444 Verify-2, numpy-vectorized c-dependence)

For (n=32,s=6): for c in {2,3,4,5}, sweep all admissible primes p<= 2*ceiling, vectorized over
all C(32,6)=906192 subsets at once (numpy). Classify the first genuine defect (beta!=0, not
antipodal) and whether it sits below/above the ceiling s^(n/(2c)).
"""
import itertools, math, sys
import numpy as np
from sympy import isprime, primitive_root

n=32; s=6

def admissible_primes_upto(n, pmax, idx_min=2):
    p=n+1; out=[]
    while p<=pmax:
        if isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: out.append(p)
        p+=n
    return out

def subgroup_idx(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    out=[]; x=1
    for i in range(n): out.append((x,i)); x=(x*zeta)%p
    return out

# Precompute all size-s index subsets once (indices into mu_n)
SUBSETS = np.array(list(itertools.combinations(range(n), s)), dtype=np.int64)  # (C, s)
C = SUBSETS.shape[0]
# Precompute beta over C for each subset and antipodal flag (p-independent!)
zc = np.exp(2j*math.pi*np.arange(n)/n)            # (n,)
BETA = np.abs(zc[SUBSETS].sum(axis=1))             # (C,)
half=n//2
SETMASK = np.zeros((C, n), dtype=bool)
rows = np.repeat(np.arange(C), s)
SETMASK[rows, SUBSETS.reshape(-1)] = True
# antipodal: for every i in T, i+half mod n in T
shifted = (SUBSETS + half) % n                     # (C,s)
ANTI = SETMASK[np.repeat(np.arange(C), s), shifted.reshape(-1)].reshape(C, s).all(axis=1)
GENUINE_OK = (BETA >= 1e-6) & (~ANTI)              # subsets that COULD be genuine (p-independent)

def first_genuine_defect_prime(c, primes, ceil):
    below=None; above=None
    for p in primes:
        elts=subgroup_idx(n,p)
        valarr=np.array([v for v,_ in elts], dtype=np.int64)   # mu_n values, indexed by idx
        Tvals = valarr[SUBSETS]                                # (C,s) values mod p
        # power sums p_1..p_c mod p, vectorized
        ok = np.ones(C, dtype=bool)
        powv = Tvals.copy()
        for j in range(1, c+1):
            # power sum_j = sum of Tvals^j mod p
            ps = powv.sum(axis=1) % p
            ok &= (ps == 0)
            if j < c:
                powv = (powv * Tvals) % p
        cand = ok & GENUINE_OK
        if cand.any():
            idxs = np.nonzero(cand)[0]
            # pick first
            wi = SUBSETS[idxs[0]].tolist()
            if p<=ceil and below is None: below=(p, wi)
            if p>ceil and above is None: above=(p, wi)
            if below is not None and (above is not None or p>ceil):
                pass
        # early stop once we have one below and have passed ceiling region
    return below, above

if __name__=="__main__":
    print(f"### numpy c-dependence  n={n} s={s}  (C={C} subsets) ###", flush=True)
    for c in [2,3,4,5]:
        ceil = s**(n/(2*c))
        pmax = int(min(ceil*2.0, 70000))
        primes = admissible_primes_upto(n, pmax)
        below, above = first_genuine_defect_prime(c, primes, ceil)
        line=f"  c={c}: ceiling=s^(n/2c)={ceil:.4g}  swept {len(primes)} primes up to {pmax}: "
        if below is None and above is None:
            line+="NO genuine defect => CLEAN"
        else:
            if below: line+=f"first defect<=ceil p={below[0]} (SUPPORTS) "
            if above: line+=f"*** defect>ceil p={above[0]} (REFUTES) *** "
        print(line, flush=True)
        if below: print(f"        witness idx={below[1]}", flush=True)
        if above: print(f"        ABOVE-CEILING witness idx={above[1]}", flush=True)
