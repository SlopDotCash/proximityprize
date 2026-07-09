#!/usr/bin/env python3
"""
probe_444_verify1_c2hunt.py

Decisive hunt for c>=2 NON-COSET defects (the binding regime) and a clean test of whether the
"c DISTINCT primes => p^c | N" step holds when c>=2. Strategy:

 - n=32, scan s in a band where defects are plausible, but restrict to subsets CONTAINING idx 0
   and use larger primes only slightly above the ceiling boundary to keep the count finite.
 - More importantly: test the GALOIS / DISTINCT-PRIME logic directly. For the argument we need
   p_1(T)=...=p_c(T)=0 mod p with these giving c distinct primes 𝔭_1..𝔭_c above p dividing beta.
   The conjugates of beta_T are sigma_a(beta)=beta(T^a) for a in (ℤ/n)^* = {odd residues}, |.|=n/2.
   p_j(T)=0 means beta(T^j)≡0 at 𝔭. For j ODD (coprime to n=2^mu), T^j is a genuine conjugate,
   giving a DISTINCT prime. For j EVEN, p_j(T)=0 is a DIFFERENT (lower) constraint, NOT a new
   conjugate prime. So the # of distinct primes = #{odd j in 1..c : p_j(T)=0}, which for the
   FIRST c sums (j=1..c) is only ~c/2 (the odd ones)!  => p^{ceil(c/2)} | N, NOT p^c | N (?).
   THIS PROBE CHECKS THAT: compare v_p(N) against c and against #odd-j-in-1..c with p_j=0.
"""
import itertools
from sympy import isprime, primitive_root, symbols, Poly, ZZ, gcd, factorint

def subgroup_with_idx(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    out=[]; x=1
    for idx in range(n): out.append((idx,x)); x=(x*zeta)%p
    return out, zeta
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
def is_antipodal_balanced(Tidx,n):
    half=n//2; S=set(i%n for i in Tidx)
    return all(((i+half)%n in S)==(i in S) for i in range(n))
def power_sum_mod_x(Tx,j,p): return sum(pow(x,j,p) for x in Tx)%p
def small_primes_1modn(n,count,start=None):
    ps=[]; p=start if start else 2*n+1
    p += (n - (p-1)%n)%n  # make p-1 divisible by n
    while len(ps)<count:
        if isprime(p) and (p-1)%n==0: ps.append(p)
        p+=n
    return ps

def hunt(n, s, k, nprimes=40, want=20, fix0=True):
    c=s-k; half=n//2; ceiling=s**(n/(2*c))
    print(f"\n##### n={n} s={s} k={k} c={c} ceiling={s}^{n/(2*c):.4g}={ceiling:.6g} #####",flush=True)
    found=0; pc_full_fail=0; pc_half_match=0
    rows=[]
    for p in small_primes_1modn(n,nprimes):
        elts,zeta=subgroup_with_idx(n,p); all_x=[x for _,x in elts]
        # restrict to subsets containing 0 (WLOG by rotation: dilation by group keeps power-sum-0)
        rest = range(1,n)
        for sub in itertools.combinations(rest, s-1):
            Tidx=[0]+list(sub); Tx=[all_x[i] for i in Tidx]
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)): continue
            if is_antipodal_balanced(Tidx,n): continue
            v=beta_vec(Tidx,n)
            if is_zero_vec(v): continue
            Nb=norm_beta(v,n); nb=abs(Nb); vp=0
            while nb and nb%p==0: nb//=p; vp+=1
            odd_vanish_in_c = sum(1 for j in range(1,c+1) if gcd(j,n)==1 and power_sum_mod_x(Tx,j,p)==0)
            found+=1
            if vp < c: pc_full_fail+=1
            if vp == odd_vanish_in_c: pc_half_match+=1
            rows.append((p,Tidx,abs(Nb),vp,c,odd_vanish_in_c, p<=ceiling, abs(Nb)<=s**half))
            if found>=want: break
        if found>=want: break
    print(f"  found {found} c={c} non-coset defects.",flush=True)
    print(f"  #(v_p < c) i.e. p^c|N FAILS: {pc_full_fail}/{found}",flush=True)
    print(f"  #(v_p == #odd-coprime-vanish-in-1..c): {pc_half_match}/{found}",flush=True)
    for (p,T,N,vp,c_,ov,dok,nok) in rows[:want]:
        print(f"    p={p} T={T} |N|={N} v_p={vp} c={c_} #odd-coprime-vanish={ov} "
              f"p^c|N:{vp>=c_} p<=ceil:{dok} |N|<=s^(n/2):{nok}",flush=True)
    return found, pc_full_fail

if __name__=="__main__":
    # n=32, c=2: need s with s-k=2. The defect requires 2 vanishing power sums.
    # j=1 (odd, coprime) and j=2 (even). Only j=1 is a genuine conjugate. Test if p^2|N or p^1|N.
    hunt(32, s=6, k=4, want=20)   # c=2 ceiling 6^8
    hunt(32, s=8, k=6, want=20)   # c=2 ceiling 8^8
    # c=3 with two odd j (1,3): j=1,2,3 -> odd coprime j in {1,3} = 2 distinct conjugates
    hunt(32, s=8, k=5, want=20)   # c=3
