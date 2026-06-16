#!/usr/bin/env python3
"""
probe_444_verify1_corrected.py

CONFIRM the corrected exponent for n=2^mu: the number of distinct primes above p dividing
beta_T is #{odd j in 1..c : p_j(T)=0 mod p}, NOT c. For the FIRST c power sums j=1..c, exactly
ceil(c/2) of them are odd (j=1,3,5,...). But ALSO p_j=0 for even j is FORCED by p_{j/2}=0 only
in special cases; generically the even-j sums are independent constraints that still must vanish
to even be a defect, yet they do NOT contribute new conjugate primes.

So the rigorous norm bound is  p^{K'} | N(beta_T),  K' = #{odd j in 1..c : p_j(T)=0 mod p}
  <= ceil(c/2)  (at most the odd j's in range, and only those coprime to n=2^mu, i.e. ALL odd j).
Actually every odd j<n is coprime to n=2^mu, so K' = #{odd j in 1..c with p_j=0}.
Since a defect needs p_1..p_c ALL =0, the odd j in 1..c are j=1,3,..,(2*ceil(c/2)-1): count=ceil(c/2).
=> p^{ceil(c/2)} | N  (the CORRECT bound), giving p <= s^{(n/2)/ceil(c/2)} = s^{n/(2 ceil(c/2))}.
This is WEAKER than the claimed p <= s^{n/(2c)} by roughly a factor 2 in the exponent.

This probe verifies v_p(N) == ceil(c/2) for c=2,3,4 defects, and recomputes the corrected ceiling.
"""
import itertools, math
from sympy import isprime, primitive_root, symbols, Poly, ZZ, gcd

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
def small_primes_1modn(n,count):
    ps=[]; p=2*n+1; p+=(n-(p-1)%n)%n
    while len(ps)<count:
        if isprime(p) and (p-1)%n==0: ps.append(p)
        p+=n
    return ps

def hunt(n,s,k,nprimes=8,want=15):
    c=s-k; half=n//2
    Kcorr = math.ceil(c/2)   # corrected exponent
    ceil_claim = s**(n/(2*c))
    ceil_corr  = s**((n/2)/Kcorr)
    print(f"\n##### n={n} s={s} k={k} c={c}  CLAIMED-exp=c={c} CORRECTED-exp=ceil(c/2)={Kcorr} #####",flush=True)
    print(f"  claimed ceiling s^(n/2c)={ceil_claim:.5g}   corrected ceiling s^((n/2)/ceil(c/2))={ceil_corr:.5g}",flush=True)
    found=0; match_corr=0; match_claim=0; norm_ok_all=0
    for p in small_primes_1modn(n,nprimes):
        elts,zeta=subgroup_with_idx(n,p); all_x=[x for _,x in elts]
        for sub in itertools.combinations(range(1,n), s-1):
            Tidx=[0]+list(sub); Tx=[all_x[i] for i in Tidx]
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)): continue
            if is_antipodal_balanced(Tidx,n): continue
            v=beta_vec(Tidx,n)
            if is_zero_vec(v): continue
            Nb=norm_beta(v,n); nb=abs(Nb); vp=0
            while nb and nb%p==0: nb//=p; vp+=1
            found+=1
            if vp==Kcorr: match_corr+=1
            if vp>=c: match_claim+=1
            if abs(Nb)<=s**half: norm_ok_all+=1
            if found>=want: break
        if found>=want: break
    print(f"  found {found} defects. v_p==ceil(c/2): {match_corr}/{found}   v_p>=c (CLAIM): {match_claim}/{found}   |N|<=s^(n/2): {norm_ok_all}/{found}",flush=True)

if __name__=="__main__":
    hunt(32, s=6, k=4)    # c=2 -> ceil=1
    hunt(32, s=8, k=5)    # c=3 -> ceil=2
    hunt(32, s=10, k=6)   # c=4 -> ceil=2
    hunt(32, s=9, k=4)    # c=5 -> ceil=3
