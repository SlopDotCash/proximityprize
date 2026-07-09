#!/usr/bin/env python3
"""
probe_444_verify1_belowceiling.py  (#444 Verify-1, the decisive test)

The window prime is huge (>>ceiling), so no defect exists there -- which only confirms the
clean side. To STRESS-TEST the argument we must go BELOW the ceiling: small primes p = 1 mod n.
For each such p we scan all size-s subsets T of mu_n with the first c power sums vanishing mod p,
and for the NON-coset ones (genuine list-defect carriers) we verify EVERY step:
  (a) is beta_T != 0 over C?  (Lam-Leung claim)   -- and hunt non-coset T with beta_T = 0.
  (b) does p^c | N(beta_T)?
  (c) |sigma(beta_T)| <= s and |N(beta_T)| <= s^{n/2}?
  (d) the master inequality: defect EXISTS  =>  p <= s^{n/(2c)}.
We also separate "c power sums vanish mod p" (the field condition) from "beta_T=0 over C"
(the char-0 / coset condition) to expose any conflation.
"""
import itertools, cmath
from sympy import isprime, primitive_root, symbols, Poly, ZZ

def subgroup_with_idx(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    out=[]; x=1
    for idx in range(n):
        out.append((idx,x)); x=(x*zeta)%p
    return out, zeta

def power_sum_mod_x(Tx,j,p):
    return sum(pow(x,j,p) for x in Tx)%p

def reduce_cyclotomic(coeffs, half):
    out=[0]*half
    for e,c in enumerate(coeffs):
        r=e%(2*half); sign=1
        if r>=half: r-=half; sign=-1
        out[r]+=sign*c
    return out

def beta_vec(Tidx,n):
    half=n//2; coeffs=[0]*n
    for idx in Tidx: coeffs[idx%n]+=1
    return reduce_cyclotomic(coeffs,half)

def is_zero_vec(v): return all(c==0 for c in v)

def norm_beta(vec,n):
    half=n//2; X=symbols('X')
    B=Poly(sum(int(vec[i])*X**i for i in range(half)),X,domain=ZZ)
    Phi=Poly(X**half+1,X,domain=ZZ)
    return int(Phi.resultant(B))

def embeddings_abs(vec,n):
    half=n//2; out=[]
    for k in range(n):
        if k%2==1:
            r=cmath.exp(2j*cmath.pi*k/n)
            out.append(abs(sum(vec[i]*(r**i) for i in range(half))))
    return out

def is_antipodal_balanced(Tidx,n):
    half=n//2; S=set(i%n for i in Tidx)
    return all(((i+half)%n in S)==(i in S) for i in range(n))

def small_primes_1modn(n, count):
    ps=[]; p=2*n+1
    while len(ps)<count:
        if isprime(p) and (p-1)%n==0: ps.append(p)
        p+=n
    return ps

def scan(n, k, s, nprimes=12):
    c=s-k; half=n//2
    ceiling = s**(n/(2*c))
    print(f"\n===== n={n} mu={n.bit_length()-1}  k={k} s={s} c=s-k={c}  ceiling=s^(n/2c)={s}^{n/(2*c):.3g}={ceiling:.6g} =====",flush=True)
    for p in small_primes_1modn(n,nprimes):
        elts,zeta=subgroup_with_idx(n,p)
        all_x=[x for _,x in elts]
        defects=[]; zero_beta_noncoset=[]; total_vanish=0
        for combo in itertools.combinations(range(n), s):
            Tidx=list(combo); Tx=[all_x[i] for i in Tidx]
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)): continue
            total_vanish+=1
            v=beta_vec(Tidx,n); bz=is_zero_vec(v); bal=is_antipodal_balanced(Tidx,n)
            if not bal:
                defects.append((Tidx,v,bz))
                if bz: zero_beta_noncoset.append(Tidx)
        genuine=[(T,v) for (T,v,bz) in defects if not bz]
        below = p<=ceiling
        flag = ""
        if genuine and not below:  flag=" <<< VIOLATION of (d): defect ABOVE ceiling!"
        if zero_beta_noncoset:     flag+=" <<< COUNTEREXAMPLE to (a): non-coset, beta=0!"
        print(f"  p={p:<8} below_ceiling={str(below):<5} #vanish={total_vanish:<3} #non-antipodal={len(defects):<3} "
              f"#genuine-defect(beta!=0)={len(genuine):<3} #(a)-ctrex={len(zero_beta_noncoset)}{flag}",flush=True)
        for (T,v) in genuine[:4]:
            Nb=norm_beta(v,n); embs=embeddings_abs(v,n); mx=max(embs)
            nb=abs(Nb); vp=0
            while nb and nb%p==0: nb//=p; vp+=1
            print(f"      defect T={T}: |N|={abs(Nb)} v_p={vp}(need>={c}:{vp>=c}) "
                  f"maxemb={mx:.3f}(<=s:{mx<=s+1e-9}) |N|<=s^(n/2)={s**half}:{abs(Nb)<=s**half} "
                  f"p<=ceil:{p<=ceiling}",flush=True)

if __name__=="__main__":
    # eta=1/8 binding config: k=n/8, s=n/4, c=n/8
    scan(16, k=2, s=4)   # ceiling 4^4=256: should see defects appear only for p<=256... but min p=17
    # Also a config with a LARGER ceiling so defects are reachable: smaller c (=less vanishing).
    # k=n/4 - 1, s=n/4 -> c=1: ceiling s^(n/2)=4^8=65536, defects reachable.
    scan(16, k=3, s=4)   # c=1, ceiling=4^8=65536
    # And a config probing the e_1=0 only (c=1) with s larger
    scan(16, k=5, s=6)   # c=1, s=6, ceiling=6^8
