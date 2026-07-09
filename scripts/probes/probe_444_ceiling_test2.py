#!/usr/bin/env python3
"""
probe_444_ceiling_test2.py  (#444 Verify-2, ceiling test v2 -- capped & verified)

(1) VERIFY the n=32 p=97 witness rigorously (exact e_1..e_c mod p, beta over C, not coset-union).
(2) For each (n=power2,s,c): find first genuine-defect prime over a CAPPED list of primes
    (first K primes p=1 mod n with m>=2), and ALSO record the largest defect prime seen, to test
    whether any genuine defect appears ABOVE the ceiling s^(n/(2c)).  Cap K so it finishes.
(3) c-DEPENDENCE: at fixed (n,s) sweep c upward, show defects vanish as c grows (clean regime).
"""
import itertools, cmath, math
from sympy import isprime, primitive_root
from math import comb

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

def power_sums(roots,p,upto):
    return [sum(pow(r,j,p) for r in roots)%p for j in range(1,upto+1)]

def beta_abs(idxs,n):
    z=2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def verify_witness():
    print("### (1) VERIFY n=32 p=97 witness idx=[0,1,2,8,12,30] ###", flush=True)
    n=32; p=97; c=2
    elts=subgroup_idx(n,p)
    valof={i:v for v,i in elts}
    T=[valof[i] for i in [0,1,2,8,12,30]]
    es=elem_sym(T,p,5); ps=power_sums(T,p,5)
    b=beta_abs([0,1,2,8,12,30],n)
    print(f"   T values mod {p}: {sorted(T)}", flush=True)
    print(f"   e_1..e_5 mod p = {es}   (e_1=e_2=0 required for c=2)", flush=True)
    print(f"   power sums p_1..p_5 mod p = {ps}", flush=True)
    print(f"   |beta_T| over C = {b:.6f}  (!=0 => GENUINE non-coset by Lam-Leung)", flush=True)
    half=n//2; Ts=set([0,1,2,8,12,30])
    antip = all(((i+half)%n) in Ts for i in [0,1,2,8,12,30])
    print(f"   antipodal (T=-T)? {antip}   (must be False to count)", flush=True)
    # also verify m=(p-1)/n
    print(f"   m=(p-1)/n = {(p-1)//n}  (proper subgroup, >=2 required)", flush=True)
    print(flush=True)

def scan(n, s, c, K):
    """Over first K admissible primes: collect all primes admitting a genuine defect."""
    half=n//2
    hits=[]
    for p in primes_1modn(n, K):
        elts=subgroup_idx(n,p)
        val=[v for v,_ in elts]; idx={v:i for v,i in elts}
        found=False; wit=None
        for T in itertools.combinations(val, s):
            if all(e==0 for e in elem_sym(T,p,c)):
                Tidx=[idx[x] for x in T]; Ts=set(Tidx)
                if all(((i+half)%n) in Ts for i in Tidx): continue
                if beta_abs(Tidx,n)>=1e-6:
                    found=True; wit=sorted(Tidx); break
        if found: hits.append((p,wit))
    return hits

if __name__=="__main__":
    verify_witness()
    print("### (2)+(3) c-dependence + ceiling.  hits = primes (first K) with a genuine defect ###", flush=True)
    # n=32: fixed s, sweep c. C(32,6)=906192, C(32,8)=10.5M(skip), use s=6 and s=7.
    K=60  # first 60 admissible primes (~ up to a few thousand for n=32)
    for n,s in [(32,6),(32,7)]:
        if comb(n,s)>4_000_000:
            print(f"  n={n} s={s}: C={comb(n,s)} skip", flush=True); continue
        print(f" -- n={n} s={s}  (sweep c; first {K} primes p=1 mod n, m>=2) --", flush=True)
        for c in range(2, s):
            ceil = s**(n/(2*c))
            hits = scan(n,s,c,K)
            if hits:
                pmin=min(h[0] for h in hits); pmax=max(h[0] for h in hits)
                above = [p for p,_ in hits if p>ceil]
                verdict = f"max defect-prime={pmax} {'<=ceil SUPPORTS' if pmax<=ceil else f'>ceil ({len(above)} above) REFUTES'}"
                print(f"    c={c}: ceiling=s^(n/2c)={ceil:.4g}  #defect-primes={len(hits)} (min={pmin})  {verdict}", flush=True)
                print(f"          first witness @p={hits[0][0]}: idx={hits[0][1]}", flush=True)
            else:
                print(f"    c={c}: ceiling={ceil:.4g}  NO genuine defect in first {K} primes (CLEAN)", flush=True)
