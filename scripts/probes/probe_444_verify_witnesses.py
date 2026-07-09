#!/usr/bin/env python3
"""
probe_444_verify_witnesses.py  (#444 Verify-2, rigorous witness verification + smallest prime)

Verify the n=32 (p=97) and n=64 defect witnesses exactly:
 - exact power sums p_1..p_c = 0 mod p
 - beta_T over C != 0 (genuine non-coset by Lam-Leung 2-power rigidity)
 - NOT antipodal, NOT a union of proper-subgroup cosets (which would force beta=0; we already
   check beta!=0, so this is automatic, but we also report the actual subgroup-decomposition test)
 - find the SMALLEST admissible prime for n=64 s=6 c=2 by exhaustive small-prime search over a
   targeted candidate family (fix 4 indices, solve power-sum constraints for the rest is hard;
   instead random+exhaust over first few primes with a denser random budget).
"""
import math, cmath, random
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

def beta_c0(idxs,n):
    z=2j*math.pi/n
    return sum(cmath.exp(z*i) for i in idxs)

def power_sums(T,p,upto):
    return [sum(pow(t,j,p) for t in T)%p for j in range(1,upto+1)]

def verify(n, p, idxs, c):
    elts=subgroup_idx(n,p); valof={i:v for v,i in elts}
    T=[valof[i] for i in idxs]
    ps=power_sums(T,p,max(c+3,5))
    b=beta_c0(idxs,n)
    half=n//2; Ts=set(idxs)
    antip=all(((i+half)%n) in Ts for i in idxs)
    # subgroup-coset-union test: T invariant under some nontrivial idx-translation t (idx->idx+t mod n)
    invariances=[t for t in range(1,n) if all(((i+t)%n) in Ts for i in idxs)]
    print(f"  n={n} p={p} c={c} idx={sorted(idxs)}  T(mod p)={sorted(T)}", flush=True)
    print(f"     power sums p_1..p_{len(ps)} = {ps}   (first {c} must be 0)", flush=True)
    print(f"     |beta_T| over C = {abs(b):.6f}  (!=0 => GENUINE non-coset)", flush=True)
    print(f"     antipodal(T=-T)? {antip}   translation-invariances (coset-union signal)={invariances}", flush=True)
    print(f"     m=(p-1)/n={(p-1)//n}", flush=True)
    ok = all(x==0 for x in ps[:c]) and abs(b)>=1e-6 and not antip
    print(f"     => GENUINE DEFECT confirmed: {ok}", flush=True)
    return ok

def smallest_prime_n64(s=6, c=2, pmax=600, budget=3_000_000):
    n=64; half=n//2; ceil=s**(n/(2*c))
    for p in admissible_primes_upto(n, pmax):
        elts=subgroup_idx(n,p); valarr=[v for v,_ in elts]
        rng=random.Random(777+p)
        for _ in range(budget):
            idxs=rng.sample(range(n), s)
            T=[valarr[i] for i in idxs]
            ps1=0; ps2=0
            for t in T: ps1=(ps1+t)%p; ps2=(ps2+t*t)%p
            if ps1==0 and ps2==0:
                Ts=set(idxs)
                if all(((i+half)%n) in Ts for i in idxs): continue
                if abs(beta_c0(idxs,n))>=1e-6:
                    return p, sorted(idxs)
    return None, None

if __name__=="__main__":
    print("### RIGOROUS WITNESS VERIFICATION ###", flush=True)
    verify(32, 97, [0,1,2,8,12,30], 2)
    verify(64, 193, [4,12,27,33,59,61], 2)
    print("\n### SMALLEST n=64 s=6 c=2 prime (denser random over first few primes) ###", flush=True)
    p,w = smallest_prime_n64()
    if p:
        ceil=6**(64/4)
        print(f"   smallest found: p={p} idx={w}  ceiling=6^16={ceil:.4g}  p<=ceil? {p<=ceil}", flush=True)
    else:
        print("   none found <=600 within budget", flush=True)
