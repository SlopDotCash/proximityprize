#!/usr/bin/env python3
"""
probe_444_verify1_identity.py

Drill into step (b)'s MECHANISM on concrete c=1 and (hunted) c>=2 defects:
  - The identity sigma_j(beta_T) ≡ p_j(T) (mod 𝔭): exact verification that the j-th Galois
    conjugate of beta_T reduces to the j-th power sum of T at the prime 𝔭 above p.
  - "c vanishing power sums => beta_T lies in c distinct primes above p => p^c | N":
    we verify v_p(N(beta_T)) >= #{1<=j<c+1 : gcd(j,n)=1 and p_j(T)=0 mod p}, i.e. count the
    coprime j among 1..c whose power sum vanishes -- those are the c distinct conjugate primes.
  - Also: how many of the j in 1..c are coprime to n?  (Only coprime j give DISTINCT Galois
    conjugates; non-coprime j give conjugates of LOWER-degree subfields -> may NOT be distinct
    primes.  THIS IS A POTENTIAL GAP in the "c distinct primes" claim.)

Also factor N(beta_T) and report v_p; check whether p^c | N truly needs c COPRIME vanishing j.
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

def analyze_defect(n,p,Tidx,zeta,all_x,s,c):
    half=n//2; Tx=[all_x[i] for i in Tidx]
    v=beta_vec(Tidx,n); Nb=norm_beta(v,n); nb=abs(Nb); vp=0
    while nb and nb%p==0: nb//=p; vp+=1
    # which power sums p_j(T) vanish mod p, for j=1..n-1, split by gcd(j,n)
    vanish=[]; vanish_coprime=[]
    for j in range(1,n):
        if power_sum_mod_x(Tx,j,p)==0:
            vanish.append(j)
            if gcd(j,n)==1: vanish_coprime.append(j)
    # the argument needs the FIRST c power sums (j=1..c) vanishing; count coprime among 1..c
    first_c_vanish=[j for j in range(1,c+1) if power_sum_mod_x(Tx,j,p)==0]
    first_c_coprime_vanish=[j for j in first_c_vanish if gcd(j,n)==1]
    # identity check sigma_j(beta)~p_j
    id_ok=all(
        sum(beta_vec_dilated(Tidx,n,j)[i]*pow(zeta,i,p) for i in range(half))%p
            == power_sum_mod_x(Tx,j,p)
        for j in range(1,n))
    print(f"  T={Tidx}: |N|={abs(Nb)} factor={factorint(abs(Nb)) if abs(Nb)<10**9 else 'big'} "
          f"v_p={vp}",flush=True)
    print(f"     vanishing power sums j (1..{n-1}): {vanish}",flush=True)
    print(f"     coprime-to-n among them: {vanish_coprime}  (count={len(vanish_coprime)})",flush=True)
    print(f"     first c={c}: vanish={first_c_vanish} coprime-vanish={first_c_coprime_vanish}",flush=True)
    print(f"     CLAIM p^c|N: {vp>=c} (c={c})  vs  v_p={vp}  vs #coprime-vanish-in-1..c={len(first_c_coprime_vanish)}",flush=True)
    print(f"     identity sigma_j(beta)=p_j mod p (all j): {id_ok}",flush=True)
    return vp, c, len(first_c_coprime_vanish)

def small_primes_1modn(n,count):
    ps=[]; p=2*n+1
    while len(ps)<count:
        if isprime(p) and (p-1)%n==0: ps.append(p)
        p+=n
    return ps

def hunt(n,k,s,nprimes=30,want=8):
    c=s-k
    print(f"\n##### n={n} k={k} s={s} c={c} : drilling defects #####",flush=True)
    cnt=0
    for p in small_primes_1modn(n,nprimes):
        elts,zeta=subgroup_with_idx(n,p); all_x=[x for _,x in elts]
        for combo in itertools.combinations(range(n),s):
            Tidx=list(combo); Tx=[all_x[i] for i in Tidx]
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)): continue
            if is_antipodal_balanced(Tidx,n): continue
            v=beta_vec(Tidx,n)
            if is_zero_vec(v): continue
            print(f"\n p={p}:",flush=True)
            analyze_defect(n,p,Tidx,zeta,all_x,s,c)
            cnt+=1
            if cnt>=want: return
    if cnt==0: print("  (no defect found)",flush=True)

if __name__=="__main__":
    # c=1 defects (plenty at n=16): drill the identity + factorization
    hunt(16,k=5,s=6, want=4)
    # c=2 defects: need to hunt harder. Larger n moderate s.
    hunt(16,k=4,s=6, want=4)   # c=2
    hunt(16,k=6,s=8, want=4)   # c=2, s=8
    hunt(16,k=5,s=8, want=4)   # c=3, s=8
