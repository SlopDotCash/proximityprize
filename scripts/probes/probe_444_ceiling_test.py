#!/usr/bin/env python3
"""
probe_444_ceiling_test.py  (#444 Verify-2, THE decisive ceiling test)

For each (n=power-of-2, s, c), sweep primes p = 1 mod n (with m=(p-1)/n >= 2, PROPER subgroup)
from SMALL upward, and find the FIRST p admitting a GENUINE non-coset defect:
   T subset mu_n, |T|=s, e_1..e_c = 0 mod p, beta_T = sum zeta_n^idx != 0 over C, T != -T.
Then compare that first-defect prime to the Action-Orbit ceiling  p_ceil = s^(n/(2c)).

The synthesis is SUPPORTED iff: first-defect prime  <=  ceiling   (defect only below ceiling).
The synthesis is REFUTED  iff: a genuine defect appears at p > ceiling.

We use moderate n where exhaustive C(n,s) is feasible for the relevant (s,c).
"""
import itertools, cmath, math
from sympy import isprime, primitive_root
from math import comb

def primes_1modn(n, idx_min=2, pmax=None, pcap=None):
    """Yield primes p with p=1 mod n, (p-1)/n>=idx_min, ascending, up to pmax (value) or pcap (count)."""
    p=n+1; cnt=0
    while True:
        if pmax is not None and p>pmax: return
        if isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min:
            yield p; cnt+=1
            if pcap is not None and cnt>=pcap: return
        p+=n

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

def first_genuine_defect(n, s, c, pmax, tol=1e-6):
    """Return (p, witness_idx, beta_abs) of FIRST genuine defect over primes p<=pmax, else None."""
    half=n//2
    for p in primes_1modn(n, idx_min=2, pmax=pmax):
        elts=subgroup_idx(n,p)
        val=[v for v,_ in elts]; idx={v:i for v,i in elts}
        for T in itertools.combinations(val, s):
            if all(e==0 for e in elem_sym(T,p,c)):
                Tidx=[idx[x] for x in T]; Ts=set(Tidx)
                if all(((i+half)%n) in Ts for i in Tidx):  # antipodal -> excluded
                    continue
                b=beta_abs(Tidx,n)
                if b>=tol:
                    return p, sorted(Tidx), b
    return None

if __name__=="__main__":
    print("### CEILING TEST: first genuine defect prime vs ceiling s^(n/(2c)) ###\n", flush=True)
    # (n, s, c) cases. Keep C(n,s) feasible. Vary c to probe wall (small c) vs clean (large c).
    cases = [
        (16, 6, 2), (16, 6, 3), (16, 6, 4),
        (16, 8, 2), (16, 8, 3), (16, 8, 4),
        (32, 6, 2), (32, 6, 3),
        (32, 8, 2), (32, 8, 3), (32, 8, 4),
        (32,10, 2), (32,10, 3),
    ]
    for (n,s,c) in cases:
        if comb(n,s) > 5_000_000:
            print(f"  n={n} s={s} c={c}: C(n,s)={comb(n,s)} too large, skip", flush=True)
            continue
        ceil = s**(n/(2*c))
        # search primes up to max(ceiling*4, n^4) so we can see whether defect appears above ceiling
        pmax = int(min(max(ceil*8, n**3), 4_000_000))
        res = first_genuine_defect(n, s, c, pmax)
        if res is None:
            print(f"  n={n} s={s} c={c}: NO genuine defect for p<= {pmax}  (ceiling={ceil:.4g})", flush=True)
        else:
            p, w, b = res
            rel = "<=ceil (SUPPORTS)" if p<=ceil else ">ceil (REFUTES)"
            print(f"  n={n} s={s} c={c}: FIRST genuine defect p={p}  ceiling=s^(n/2c)={ceil:.4g}  -> {rel}", flush=True)
            print(f"        witness idx={w} |beta|={b:.4f}", flush=True)
