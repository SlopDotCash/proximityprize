#!/usr/bin/env python3
"""
probe_444_verify1_normbound.py  (#444 Verify-1)

Independently re-derive & CHECK the Action-Orbit norm bound applied to the descent's
list-defect. For a NON-coset size-s subset T of mu_n (n=2^mu) with the first c power sums
vanishing mod p:
  (a) beta_T != 0 over C for non-coset T?  (Lam-Leung)
  (b) do c DISTINCT primes above p divide beta_T (= power sums mod p -> Galois conjugates 0 mod p)?
  (c) |sigma(beta_T)| <= s  and  |N(beta_T)| <= s^{n/2} ?
  (d) NUMERIC: whenever a non-coset defect exists, does p <= s^{n/(2c)} hold?

Uses exact arithmetic. beta_T lives in ℤ[ζ_n] = ℤ[X]/Φ_n, Φ_n = X^{n/2}+1 for n=2^mu.
We represent algebraic integers by their coefficient vector in the power basis 1,ζ,...,ζ^{n/2-1}.
"""
import itertools
from sympy import isprime, primitive_root, factorint, Poly, symbols, ZZ
from sympy import nextprime

# ---------- field-side helpers ----------
def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup_with_idx(n,p):
    """Return list of (idx, x) where x = zeta^idx, idx in 0..n-1, zeta a fixed primitive n-th root."""
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    out=[]; x=1
    for idx in range(n):
        out.append((idx, x)); x=(x*zeta)%p
    return out, zeta

def power_sum_mod(Tidx, zeta, j, p):
    """Sum over x in T of x^j mod p, where x = zeta^idx."""
    return sum(pow(zeta, (idx*j) % ( (p-1) ), p) for idx in Tidx) % p
    # note: zeta^idx has order dividing n; zeta^{idx*j} fine mod p

# safer power-sum: directly with x values
def power_sum_mod_x(Tx, j, p):
    return sum(pow(x, j, p) for x in Tx) % p

# ---------- cyclotomic algebraic-integer side (n=2^mu, Phi_n = X^{n/2}+1) ----------
def reduce_cyclotomic(coeffs, half):
    """coeffs is a list of length up to n (exponents 0..n-1). Reduce mod X^{half}+1 (X^{half}=-1).
       Returns vector length `half`."""
    out=[0]*half
    for e,c in enumerate(coeffs):
        r=e % (2*half); sign=1
        if r>=half: r-=half; sign=-1
        out[r]+=sign*c
    return out

def beta_vec(Tidx, n):
    """beta_T = sum_{idx in T} ζ^idx in ℤ[ζ_n], reduced in power basis dim n/2."""
    half=n//2
    coeffs=[0]*n
    for idx in Tidx: coeffs[idx % n]+=1
    return reduce_cyclotomic(coeffs, half)

def is_zero_vec(v): return all(c==0 for c in v)

# Norm of beta in ℤ[ζ_n]: N(beta) = prod over the phi(n)=n/2 embeddings sigma_j(beta),
# = Res(Phi_n(X), B(X)) up to sign where B(X) = sum coeffs X^i. We compute it as the
# product of B(root) over roots of Phi_n, i.e. the resultant. Use integer resultant.
def norm_beta(vec, n):
    half=n//2
    X=symbols('X')
    B=Poly(sum(int(vec[i])*X**i for i in range(half)), X, domain=ZZ)
    Phi=Poly(X**half+1, X, domain=ZZ)
    # N(beta) = Res(Phi, B) (= prod_{Phi(r)=0} B(r)); for monic Phi this equals the field norm
    res = Phi.resultant(B)
    return int(res)

# embeddings |sigma_j(beta)|: roots of Phi_n are exp(i*pi*(2j+1)/n)? Phi_{2^mu}=X^{n/2}+1, roots
# are the primitive n-th roots of unity = exp(2pi i k /n), k odd. |sigma(beta)| via complex eval.
import cmath
def embeddings_abs(vec, n):
    half=n//2
    out=[]
    for k in range(n):
        if k%2==1:  # primitive n-th roots
            r=cmath.exp(2j*cmath.pi*k/n)
            val=sum(vec[i]*(r**i) for i in range(half))
            out.append(abs(val))
    return out  # length n/2

# ---------- non-coset / antipodal test ----------
def is_coset_union(Tidx, n):
    """T is a union of cosets of some nontrivial subgroup? We test specifically: is T a union of
       cosets of the order-2 subgroup {0, n/2} (antipodal pairs)?  i.e. idx in T <=> idx+n/2 in T.
       (Lam-Leung char-0: e_1(T)=0 over C <=> antipodal-balanced.)"""
    half=n//2; S=set(i%n for i in Tidx)
    return all(((i+half)%n in S) == (i in S) for i in range(n))

# ---------- main scans ----------
def scan(n, betas=(4.0,4.5)):
    print(f"\n===== n={n} (mu={n.bit_length()-1}) =====", flush=True)
    half=n//2
    for beta in betas:
        p=find_window_prime(n,beta)
        elts,zeta=subgroup_with_idx(n,p)
        idx_of={x:idx for idx,x in elts}
        # We scan subsets T of size s with the first c power sums vanishing mod p.
        # Use the descent's eta=1/8 binding config from probe_444: k=n/8, s=n/4, c=s-k=n/8.
        k=n//8; s=n//4; c=s-k  # c = n/8
        print(f"  beta={beta} p={p} k={k} s={s} c(=s-k)={c}", flush=True)
        # ceiling: defect requires p <= s^{n/(2c)}
        ceiling = s**(n//(2*c)) if (n%(2*c)==0) else s**(n/(2*c))
        print(f"    norm ceiling s^(n/(2c)) = {s}^{n/(2*c)} = {ceiling:.4g}; p={p} {'<=' if p<=ceiling else '>'} ceiling", flush=True)
        all_idx=[idx for idx,_ in elts]
        all_x=[x for _,x in elts]
        defects=[]              # non-coset T with c power sums vanishing
        zero_beta_noncoset=[]   # COUNTEREXAMPLES to (a): non-coset T with beta_T=0
        nonzero_coset=[]        # coset T with beta_T!=0 (sanity)
        examined=0
        for combo in itertools.combinations(range(n), s):
            Tidx=list(combo)
            Tx=[all_x[i] for i in Tidx]
            # check first c power sums vanish mod p
            if not all(power_sum_mod_x(Tx,j,p)==0 for j in range(1,c+1)):
                continue
            examined+=1
            v=beta_vec(Tidx,n)
            bz=is_zero_vec(v)
            coset=is_coset_union(Tidx,n)
            if not coset:
                defects.append((Tidx,v,bz))
                if bz: zero_beta_noncoset.append(Tidx)
            else:
                if not bz: nonzero_coset.append(Tidx)
        print(f"    #subsets with c power-sums=0 mod p (examined): {examined}", flush=True)
        print(f"    #NON-coset among them (candidate defects): {len(defects)}", flush=True)
        print(f"    (a) #non-coset with beta_T=0 over C (COUNTEREXAMPLES to step a): {len(zero_beta_noncoset)}", flush=True)
        print(f"    (sanity) #coset-union T with beta_T!=0 over C: {len(nonzero_coset)}", flush=True)
        # For each genuine defect (non-coset, beta!=0) verify (b)(c)(d)
        for Tidx,v,bz in defects[:6]:
            if bz:
                continue
            Nb=norm_beta(v,n)
            embs=embeddings_abs(v,n)
            maxemb=max(embs)
            # (c) per-embedding |sigma(beta)| <= s ?
            cbound_ok = maxemb <= s + 1e-9
            # |N| <= s^{n/2} ?
            normbound_ok = abs(Nb) <= s**half
            # (b) p^c | N(beta) ?
            vp = 0
            nb=abs(Nb)
            if nb!=0:
                while nb % p == 0:
                    nb//=p; vp+=1
            pc_div_ok = vp >= c
            # (d) p <= s^{n/(2c)} when defect exists
            d_ok = p <= ceiling
            print(f"      DEFECT idx={Tidx}: |N|={abs(Nb)}  v_p(N)={vp} (need>={c}: {pc_div_ok})  "
                  f"maxemb={maxemb:.3f} (<=s={s}:{cbound_ok})  |N|<=s^(n/2)={s**half}:{normbound_ok}  "
                  f"p<=ceiling:{d_ok}", flush=True)
        if not any(not bz for _,_,bz in defects):
            print("    -> NO genuine non-coset defect found (consistent with 'no defect above ceiling').", flush=True)

if __name__=="__main__":
    scan(16)
    # n=32 is C(32,8)=10518300 subsets -> too many for the full power-sum scan; do a targeted version
    print("\n[n=32 full scan skipped: C(32,8)=10.5M subsets. Run probe_444_verify1_n32.py for targeted.]", flush=True)
