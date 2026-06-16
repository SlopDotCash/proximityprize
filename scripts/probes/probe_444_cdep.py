#!/usr/bin/env python3
"""
probe_444_cdep.py  (#444 Verify-2, the c-DEPENDENCE decisive test, fast)

Fix (n=32, s=6). Sweep c=2,3,4,5. For a SMALL set of primes, find the first genuine defect.
The synthesis predicts: genuine defects at SMALL c (wall, high ceiling) but NOT at LARGE c
(clean, low ceiling). And every defect-prime <= ceiling s^(n/(2c)).
Fast: early-exit per prime on first genuine witness.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

def primes_1modn(n, K, idx_min=2):
    p=n+1; out=[]
    while len(out)<K:
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

def first_defect_over_primes(n,s,c,primes):
    half=n//2
    for p in primes:
        elts=subgroup_idx(n,p)
        val=[v for v,_ in elts]; idx={v:i for v,i in elts}
        for T in itertools.combinations(val, s):
            if all(e==0 for e in elem_sym(T,p,c)):
                Tidx=[idx[x] for x in T]; Ts=set(Tidx)
                if all(((i+half)%n) in Ts for i in Tidx): continue
                if beta_abs(Tidx,n)>=1e-6:
                    return p, sorted(Tidx)
    return None

if __name__=="__main__":
    n=32; s=6
    primes=primes_1modn(n, 25)   # first 25 admissible primes
    print(f"### c-DEPENDENCE  n={n} s={s}  primes={primes[:6]}...{primes[-1]} (first {len(primes)}) ###", flush=True)
    for c in range(2, s):
        ceil = s**(n/(2*c))
        res = first_defect_over_primes(n,s,c,primes)
        if res is None:
            print(f"  c={c}: ceiling=s^(n/2c)={ceil:.4g}  NO genuine defect in primes<= {primes[-1]}  => CLEAN", flush=True)
        else:
            p,w=res
            rel = "<=ceil SUPPORTS" if p<=ceil else ">ceil REFUTES"
            print(f"  c={c}: ceiling={ceil:.4g}  FIRST defect p={p} {rel}  witness idx={w}", flush=True)
