"""
C001 attack: n-core nonemptiness = NVM minor vanishing = list-decoding-beyond-Johnson shape.

The in-tree theorems (axiom-clean, verified by reading the Lean):
  homds_det_ne_zero_iff_nCoreEmpty : det(zeta^(beta_j * i))_{i,j in Fin n} != 0
     <=> n-core of (beta_j) empty <=> beta_j distinct mod n.
  rectBeta_nCoreEmpty_iff : for rectangle a^h, 0<h<n: n-core empty <=> n | a.

So the LINEAR-ALGEBRA half (F17 minor <=> n|a for rectangles) is genuinely PROVEN.

The CONNECTION's substantive claim is the *triple identification* F17 = F4 = F15:
  "the list-decoding obstruction shapes (F4) are exactly these interior rectangles with n|/a,
   which have NONEMPTY core => vanishing minor => the certificate is silent."
And attack_plan asks: is an adversarial rectangle a^L with n|/a actually REACHABLE by a
genuine window-radius RS[mu_n,k] list-decoding instance (a real codeword configuration)?

This probe pins, by EXACT arithmetic at proper-subgroup prize-regime primes:

 (Q1) STRUCTURE of the in-tree minor: it is the FULL n x n Vandermonde over ALL n beta-numbers
      and ALL n powers i=0..n-1. Its non-vanishing <=> beta distinct mod n is the cyclic
      degree-collapse d -> d mod n -- it is NOT a (k+1)x(k+1) list-decoding minor and does not
      see k at all. Test: vary k; minor verdict is k-independent.

 (Q2) REACHABILITY: enumerate ACTUAL RS[mu_n,k] list-decoding lists at radius in the window.
      A list of L codewords agreeing on a pattern gives, via GM-MDS, a beta-set. Does a
      reachable list ever induce a rectangle a^L with n|/a (nonempty core, vanishing minor)?
      We measure the real list sizes and whether they are "beyond Johnson", and whether the
      in-tree minor verdict tracks list-size-large vs list-size-small.
"""
import itertools, math
from fractions import Fraction

# ---- exact field arithmetic mod prime p, with mu_n a PROPER subgroup of F_p^* ----

def find_subgroup_prime(n, beta_min=4, beta_max=6, count=3):
    """primes p = 1 mod n (so mu_n proper subgroup exists), p ~ n^beta, beta in [4,6]."""
    out=[]
    lo = n**beta_min
    hi = n**beta_max
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi and len(out)<count:
        if is_prime(p) and p % n == 1 and p > n:   # proper: p-1 = n*m, m>1
            out.append(p)
        p += n
    return out

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def gen_subgroup(p, n):
    """return list of the n n-th roots of unity in F_p (a generator's powers)."""
    # find element g of order exactly n
    m = (p-1)//n
    # take primitive root then raise to m
    pr = primitive_root(p)
    z = pow(pr, m, p)              # order n
    mu = [pow(z, i, p) for i in range(n)]
    assert len(set(mu))==n, "mu_n not size n"
    return z, mu

def primitive_root(p):
    if p==2: return 1
    fac = factorize(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac):
            return g
    raise RuntimeError

def factorize(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def detmod(M, p):
    """determinant of integer matrix M mod prime p, exact (fraction-free Bareiss mod p)."""
    M=[row[:] for row in M]
    nn=len(M); det=1
    for c in range(nn):
        piv=None
        for r in range(c,nn):
            if M[r][c]%p!=0: piv=r; break
        if piv is None: return 0
        if piv!=c:
            M[c],M[piv]=M[piv],M[c]; det=(-det)%p
        inv=pow(M[c][c],p-2,p)
        det=det*M[c][c]%p
        for r in range(c+1,nn):
            f=M[r][c]*inv%p
            if f:
                for k in range(c,nn):
                    M[r][k]=(M[r][k]-f*M[c][k])%p
    return det%p

# =====================================================================
# Q1: the in-tree minor is the FULL n x n Vandermonde, k-independent.
# =====================================================================
print("="*70)
print("Q1: structure of the in-tree HOMDS minor det(zeta^(beta_j * i))_{Fin n x Fin n}")
print("="*70)

def rectBeta(n,a,h):
    return [ (a if j<h else 0) + (n-1-j) for j in range(n)]

def homds_det_rect(p, z, n, a, h):
    # M[i][j] = z^(beta_j * i) mod p, i,j in 0..n-1
    beta=rectBeta(n,a,h)
    M=[[pow(z, (beta[j]*i)%(p-1) if False else beta[j]*i, p) for j in range(n)] for i in range(n)]
    return detmod(M,p)

for n in (8,16,32):
    ps=find_subgroup_prime(n)
    if not ps: continue
    p=ps[0]; z,mu=gen_subgroup(p,n)
    print(f"\n n={n}  p={p} (p~n^{math.log(p,n):.2f}, m=(p-1)/n={(p-1)//n})  proper-subgroup")
    for h in (3, n//2):
        for a in (n, n+1, 2*n, 2*n+3):  # n|a vs n|/a
            d=homds_det_rect(p,z,n,a,h)
            ncore_empty = (n % 1==0) and (a % n==0)  # by theorem rectBeta_nCoreEmpty_iff (0<h<n)
            verdict = "det!=0(core empty)" if d!=0 else "det=0(core nonempty)"
            agree = (d!=0) == (a%n==0)
            print(f"   h={h:2d} a={a:3d} (n{'|' if a%n==0 else '/'}a)  det={'0' if d==0 else 'nz'}  -> {verdict}  matches n|a? {agree}")
