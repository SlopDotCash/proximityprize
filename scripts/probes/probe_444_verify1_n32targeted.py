#!/usr/bin/env python3
"""
probe_444_verify1_n32targeted.py

n=32 targeted: full C(32,s) is too big for large s. We do two things:
 (1) For SMALL s (s=4: c=s-k; pick k so c>=2), enumerate C(32,4)=35960 subsets -> fast.
     This finds c=2,3 non-coset defects at n=32 and tests p^c|N, |N|<=s^{n/2}, identity, ceiling.
 (2) Verify the CORE IDENTITY sigma_j(beta_T) ≡ p_j(T) (mod 𝔭) exactly (it underlies step b),
     where p_j(T)=Σ_{x∈T} x^j mod p and sigma_j(beta)=beta of dilation T^j.
"""
import itertools, cmath
from sympy import isprime, primitive_root, symbols, Poly, ZZ

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

def beta_vec_dilated(Tidx,n,j):
    half=n//2; coeffs=[0]*n
    for idx in Tidx: coeffs[(j*idx)%n]+=1
    return reduce_cyclotomic(coeffs,half)
def beta_vec(Tidx,n): return beta_vec_dilated(Tidx,n,1)
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
    ps=[]; p=2*n+1
    while len(ps)<count:
        if isprime(p) and (p-1)%n==0: ps.append(p)
        p+=n
    return ps

def scan(n,k,s,nprimes=10,maxshow=6):
    c=s-k; half=n//2; ceiling=s**(n/(2*c))
    print(f"\n===== n={n} k={k} s={s} c={c}  ceiling={s}^{n/(2*c):.4g}={ceiling:.6g} =====",flush=True)
    nshown_total=0; n_defects=0; n_ctrex_a=0; n_viol_d=0; n_id_fail=0; n_pc_fail=0; n_norm_fail=0
    for p in small_primes_1modn(n,nprimes):
        elts,zeta=subgroup_with_idx(n,p); all_x=[x for _,x in elts]
        shown=0
        for combo in itertools.combinations(range(n),s):
            Tidx=list(combo); Tx=[all_x[i] for i in Tidx]
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)): continue
            if is_antipodal_balanced(Tidx,n): continue
            v=beta_vec(Tidx,n)
            if is_zero_vec(v):
                n_ctrex_a+=1   # non-antipodal but beta=0 -> COUNTEREXAMPLE to (a)
                continue
            n_defects+=1
            Nb=norm_beta(v,n); nb=abs(Nb); vp=0
            while nb and nb%p==0: nb//=p; vp+=1
            # identity check
            id_ok=True
            for j in range(1,2*c,2):
                if j>=n: break
                vj=beta_vec_dilated(Tidx,n,j)
                img=sum(vj[i]*pow(zeta,i,p) for i in range(half))%p
                if img!=power_sum_mod_x(Tx,j,p): id_ok=False
            pc_ok=(vp>=c); norm_ok=(abs(Nb)<=s**half); d_ok=(p<=ceiling)
            if not id_ok: n_id_fail+=1
            if not pc_ok: n_pc_fail+=1
            if not norm_ok: n_norm_fail+=1
            if not d_ok: n_viol_d+=1
            if shown<maxshow and nshown_total<24:
                print(f"  p={p:<7} c={c} T={Tidx}: |N|={abs(Nb)} v_p={vp}(p^c|N:{pc_ok}) "
                      f"id:{id_ok} |N|<=s^(n/2):{norm_ok} p<=ceil:{d_ok}",flush=True)
                shown+=1; nshown_total+=1
    print(f"  SUMMARY: #genuine-defects={n_defects}  (a)ctrex(beta=0,noncoset)={n_ctrex_a}  "
          f"(b)p^c|N FAIL={n_pc_fail}  (c)|N|>s^(n/2) FAIL={n_norm_fail}  "
          f"identity FAIL={n_id_fail}  (d)ceiling VIOLATION={n_viol_d}",flush=True)

if __name__=="__main__":
    # n=32, small s so C(32,s) tractable, c=s-k>=2
    scan(32, k=2, s=4)   # c=2 ceiling=4^8=65536
    scan(32, k=1, s=4)   # c=3 ceiling=4^(32/6)=4^5.33
    scan(32, k=2, s=5)   # c=3 ceiling=5^5.33
    scan(32, k=1, s=5)   # c=4 ceiling=5^4
