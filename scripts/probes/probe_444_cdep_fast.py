#!/usr/bin/env python3
"""
probe_444_cdep_fast.py  (#444 Verify-2, c-dependence, ceiling-capped prime sweep, faster)

For (n=32,s=6): for each c in {3,4,5}, sweep ALL admissible primes p (=1 mod n, m>=2) up to the
ceiling s^(n/(2c)) (the regime where a defect, if any, would be ceiling-OBEYING), plus a margin
ABOVE the ceiling, to test BOTH:
   (a) is there a genuine defect at all below the ceiling? (if none -> clean at this c)
   (b) is there any genuine defect ABOVE the ceiling? (would REFUTE)
Speed: vectorized power-sum/elem-sym via precomputed powers per prime; early-exit per prime.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

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

def elem_sym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]

def beta_abs(idxs,n):
    z=2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def scan_prime(n,s,c,p):
    """Return first genuine witness idx for this prime, else None."""
    half=n//2
    elts=subgroup_idx(n,p)
    val=[v for v,_ in elts]; idx={v:i for v,i in elts}
    for T in itertools.combinations(val, s):
        es=elem_sym(T,p,c)
        if es[0]==0 and all(e==0 for e in es):
            Tidx=[idx[x] for x in T]; Ts=set(Tidx)
            if all(((i+half)%n) in Ts for i in Tidx): continue
            if beta_abs(Tidx,n)>=1e-6:
                return sorted(Tidx)
    return None

if __name__=="__main__":
    n=32; s=6
    print(f"### c-DEPENDENCE (ceiling-capped)  n={n} s={s} ###", flush=True)
    for c in [3,4,5]:
        ceil = s**(n/(2*c))
        # sweep primes up to 2x ceiling (so we can also catch any defect just above ceiling)
        pmax = int(min(ceil*2, 60000))
        primes = admissible_primes_upto(n, pmax)
        below=[]; above=[]
        for p in primes:
            w = scan_prime(n,s,c,p)
            if w is not None:
                (below if p<=ceil else above).append((p,w))
        if not below and not above:
            print(f"  c={c}: ceiling=s^(n/2c)={ceil:.4g}  swept {len(primes)} primes up to {pmax}: "
                  f"NO genuine defect at all => CLEAN at c={c}", flush=True)
        else:
            msg=""
            if below: msg+=f"  defect<=ceil: min p={below[0][0]} (count {len(below)})"
            if above: msg+=f"  *** DEFECT ABOVE CEILING: p={above[0][0]} (count {len(above)}) REFUTES ***"
            print(f"  c={c}: ceiling={ceil:.4g} swept {len(primes)} primes up to {pmax}:{msg}", flush=True)
            if below: print(f"        witness@{below[0][0]}: {below[0][1]}", flush=True)
            if above: print(f"        ABOVE witness@{above[0][0]}: {above[0][1]}", flush=True)
