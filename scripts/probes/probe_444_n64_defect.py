#!/usr/bin/env python3
"""
probe_444_n64_defect.py  (#444 Verify-2, n=64 defect onset via targeted construction)

C(64,s) is too large to enumerate. Instead CONSTRUCT genuine defect candidates:
A size-s subset T of mu_64 with e_1=e_2=0 mod p (c=2) and beta_T!=0 over C, not antipodal.
Method: enumerate over the n=64 index set but only size-6 subsets sampled/structured, OR
lift the verified n=32 witness {0,1,2,8,12,30} to n=64 by the doubling embedding idx->2*idx
(mu_32 <= mu_64 as the squares), which preserves vanishing power sums and beta!=0 -- then it is
a defect supported on mu_32<mu_64 (still a genuine non-coset of mu_64). We ALSO do a brute random
search for s=6 genuine defects directly in mu_64 to find the smallest prime.

Report smallest prime with a genuine n=64 defect and whether p<=ceiling s^(n/(2c))=6^(64/4)=6^16.
"""
import itertools, math, random
import numpy as np
from sympy import isprime, primitive_root

n=64

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

def beta_abs(idxs,n):
    z=2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))
import cmath

def lift_check():
    """Lift n=32 witness {0,1,2,8,12,30} into mu_64 via idx->2*idx (mu_32 = squares in mu_64)."""
    print("### (A) LIFT n=32 witness to mu_64 (idx*2) ###", flush=True)
    base=[0,1,2,8,12,30]; lifted=[2*i for i in base]  # in mu_64 indices
    s=len(lifted)
    half=n//2; Ts=set(lifted)
    antip=all(((i+half)%n) in Ts for i in lifted)
    b=beta_abs(lifted,n)
    # find smallest prime where e_1=e_2=0
    c=2; ceil = s**(n/(2*c))
    primes=admissible_primes_upto(n, 5000)
    hit=None
    for p in primes:
        elts=subgroup_idx(n,p); valof={i:v for v,i in elts}
        T=[valof[i] for i in lifted]
        ps1=sum(T)%p; ps2=sum((t*t)%p for t in T)%p
        if ps1==0 and ps2==0:
            hit=p; break
    print(f"   lifted idx={lifted}  |beta|={b:.4f}  antipodal={antip}  ceiling=6^16={ceil:.4g}", flush=True)
    if hit: print(f"   smallest prime with e_1=e_2=0: p={hit}  p<=ceiling? {hit<=ceil}", flush=True)
    else:   print(f"   no e1=e2=0 prime <=5000 for this exact lift (lift may need a tuned offset)", flush=True)

def random_search(s=6, c=2, tries_per_prime=400000, pmax=2000):
    """Random size-s subsets of mu_64; find smallest prime admitting a genuine defect."""
    print(f"### (B) RANDOM genuine-defect search  n=64 s={s} c={c}  ###", flush=True)
    primes=admissible_primes_upto(n, pmax)
    half=n//2
    ceil=s**(n/(2*c))
    for p in primes:
        elts=subgroup_idx(n,p); valarr=[v for v,_ in elts]
        rng=random.Random(12345+p)
        for _ in range(tries_per_prime):
            idxs=rng.sample(range(n), s)
            T=[valarr[i] for i in idxs]
            ps1=0; ps2=0
            for t in T:
                ps1=(ps1+t)%p; ps2=(ps2+t*t)%p
            if ps1==0 and ps2==0:
                Ts=set(idxs)
                if all(((i+half)%n) in Ts for i in idxs): continue
                if beta_abs(idxs,n)>=1e-6:
                    print(f"   FIRST genuine defect p={p}: idx={sorted(idxs)} "
                          f"ceiling=6^16={ceil:.4g}  p<=ceil? {p<=ceil}", flush=True)
                    return p
        # report progress
    print(f"   no genuine defect found by random search up to p={pmax}", flush=True)
    return None

if __name__=="__main__":
    lift_check()
    random_search()
