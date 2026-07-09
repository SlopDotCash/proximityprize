#!/usr/bin/env python3
"""
probe_444_genuine_defect_search.py  (#444 Verify-2, the corrected decisive test)

A GENUINE non-coset defect (the exact hypothesis of the Action-Orbit norm bound, Sweep_A10) is:
   a subset T of mu_n  with
     (1) the first c elementary-symmetric e_1..e_c VANISHING mod p, and
     (2) beta_T = sum_{x in T} zeta_n^{idx(x)}  !=  0  OVER C  (Lam-Leung non-coset),
   and we EXCLUDE the correlated antipodal case T=-T (the honesty contract's x^{n/2}=+-1).

n must be a POWER OF 2 (the prize regime; Lam-Leung rigidity is clean only there).
For such a genuine defect, the bound says c distinct primes above p divide beta_T, so
   p^c | N(beta_T)  <=  |T|^{phi(n)} = s^{n/2},  hence  p <= s^{n/(2c)}.
KEY QUESTION: when the FIRST genuine defect appears, does p <= s^{n/(2c)} hold?
And do genuine defects appear at SMALL c (wall) but not LARGE c (clean)?
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
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

def beta_char0_abs(idxs, n):
    z=2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def search(n, p, s, c, tol=1e-6, cap=5):
    """Return (n_lacunary, n_betazero, n_antipodal, genuine_witnesses[:cap])."""
    elts=subgroup_idx(n,p)
    val=[v for v,_ in elts]; idx={v:i for v,i in elts}
    half=n//2
    nlac=0; nbz=0; nanti=0; gen=[]
    for T in itertools.combinations(val, s):
        if all(e==0 for e in elem_sym(T,p,c)):
            nlac+=1
            Tidx=[idx[x] for x in T]; Ts=set(Tidx)
            antip = all(((i+half)%n) in Ts for i in Tidx)
            b0=beta_char0_abs(Tidx,n)
            if antip: nanti+=1
            if b0<tol: nbz+=1
            # GENUINE: beta_T != 0 over C  AND  not antipodal
            if b0>=tol and not antip:
                if len(gen)<cap: gen.append((sorted(Tidx), b0))
    return nlac, nbz, nanti, gen

if __name__=="__main__":
    from math import comb
    print("### GENUINE non-coset defect search (n = power of 2; beta_T!=0 over C; T != -T) ###", flush=True)
    print("### Ceiling: p <= s^(n/(2c)).  Question: any genuine defect? does it obey ceiling? ###\n", flush=True)
    for n in [16, 32, 64]:
        p=find_window_prime(n,4.0)
        print(f"--- n={n}  p={p}  (p~n^4, log2 p={math.log2(p):.1f}) ---", flush=True)
        smax = n//2
        any_gen=False
        for s in range(3, smax+1):
            if comb(n,s) > 6_000_000:
                continue
            for c in range(2, s):
                nlac,nbz,nanti,gen = search(n,p,s,c)
                ceil = s**(n/(2*c))
                if gen:
                    any_gen=True
                    obeys = (p <= ceil)
                    print(f"   s={s} c={c}: lacunary={nlac} (betazero={nbz} antipodal={nanti}) "
                          f"GENUINE={len(gen)}  ceiling=s^(n/2c)={ceil:.4g} p<=ceil?{obeys}", flush=True)
                    for Tidx,b0 in gen[:2]:
                        print(f"        witness idx={Tidx} |beta|={b0:.4f}", flush=True)
        if not any_gen:
            print("   NO genuine non-coset defect at any (s,c) searched.", flush=True)
        print(flush=True)
