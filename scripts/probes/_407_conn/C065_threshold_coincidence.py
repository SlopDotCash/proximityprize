"""
C065 attack: is (2r)^{phi(n)} = p the EXACT common crossover for
  (a) E_r(mu_n)  [additive energy / N0 defect],   F16/F5
  (b) max_h |T_h|  [tangent sum departing char-0 Jacobi value],  F6
both pinned to the resultant/norm threshold (2r)^{phi(n)} = p (F12)?

Prize regime: dyadic mu_n = order-n subgroup of F_q*, n = 2^mu PROPER subgroup,
q prime, q ~ n^beta. We test several proper-subgroup primes.

We compute, EXACTLY (integer arithmetic), for each (n, p):
  - r_E   : smallest r with E_r(mu_n) > E_r^{(0)}  (char-0 antipodal value)
  - r_T   : smallest r with max_h |T_h| != char-0 Jacobi value
            (T_h over ker(chi^h)?? -- careful: tangent sum is a per-h scalar,
             not naturally r-indexed.  We instead test the threshold's claim
             that T_h leaves char-0 iff a spurious <=2r-tuple exists.)
  - r_N   : smallest r with (2r)^{phi(n)} >= p   (norm threshold crossed)

The DECISIVE test for the claim "all three cross at (2r)^{phi(n)}=p":
  compare r_E vs r_N.  The PROVEN direction (no_spurious_tuple_of_lt_prime)
  guarantees r_E >= r_N  (clean below threshold).  The CLAIM ("EXACT crossover")
  additionally needs r_E == r_N (defect appears AS SOON AS threshold crossed).
  If r_E >> r_N strictly, the threshold is only NECESSARY, not the crossover.

For T_h: the tangent sum is a SINGLE scalar per character h; it is NOT indexed
by r.  Its char-0 ("archimedean Jacobi-equidistributed") value vs its actual
char-p value is a fixed number for each (n,p).  The "(2r)^{phi(n)}=p crossover"
language for T_h is the claim's weakest link -- T_h has no r.  We test the
actual content: does max_h|T_h| deviate from its char-0 prediction, and is that
deviation governed by the SAME norm threshold?  We just report the actual
max_h|T_h| and its char-0 Jacobi-average prediction for the same primes.
"""
import itertools, math, sys
from math import comb

def euler_phi(n):
    r = n; p = 2; m = n
    res = n
    pp = 2
    x = n
    result = n
    f = n
    # simple factorization
    result = n
    temp = n
    d = 2
    primes = []
    while d*d <= temp:
        if temp % d == 0:
            primes.append(d)
            while temp % d == 0:
                temp//=d
        d+=1
    if temp>1: primes.append(temp)
    res = n
    for q in primes:
        res -= res//q
    return res

def subgroup(n, p):
    """order-n multiplicative subgroup of F_p* (p prime, n | p-1)."""
    assert (p-1) % n == 0
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # element of order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x*h)%p
    assert len(set(S))==n, (n,p,len(set(S)))
    return S, h

def primitive_root(p):
    if p==2: return 1
    phi = p-1
    # factor phi
    temp=phi; fac=[]; d=2
    while d*d<=temp:
        if temp%d==0:
            fac.append(d)
            while temp%d==0: temp//=d
        d+=1
    if temp>1: fac.append(temp)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    raise RuntimeError("no primitive root")

def E_r(S, p, r):
    """additive energy E_r = #{(x_1..x_r,y_1..y_r) in S^{2r} : sum x = sum y}.
       Compute via convolution of the r-fold sumset distribution mod p."""
    n=len(S)
    # distribution of sum of r elements of S, as a dict residue->count
    from collections import Counter
    dist = Counter({0:1})
    for _ in range(r):
        nd=Counter()
        for res,c in dist.items():
            for s in S:
                nd[(res+s)%p]+=c
        dist=nd
    # E_r = sum over residues of count^2
    return sum(c*c for c in dist.values())

def E_r_char0(S, p, r):
    """char-0 value: same but NO reduction mod p -- count exact integer
       equalities sum x_i = sum y_j over integers (lift S to {1..p-1})?
       NO: char-0 means roots of unity, sum_i zeta^{a_i} = sum_j zeta^{b_j}.
       The honest char-0 reference is the additive energy of the ABSTRACT
       n-th roots of unity in C (no mod p).  We compute it as #{(a,b) in
       (Z/n)^{2r}: sum zeta_n^{a_i} = sum zeta_n^{b_j}} via exact roots count.
       For n=2^mu, Lam-Leung => only antipodal pairings vanish; but here we
       want the FULL energy (not just z=0), i.e. equality of the two sums in C.
       Equivalent integer encoding: represent zeta_n^a in the basis 1,zeta,...,
       zeta^{phi(n)-1}.  We compute the multiset of vector sums."""
    n=len(S)  # = order
    # exponents 0..n-1 ; zeta_n^k in Z[zeta_n], coordinates in cyclotomic basis.
    # For n=2^mu, phi=n/2, minimal poly X^{n/2}+1, so zeta^{n/2}=-1.
    # coordinate vector of zeta^k (k in 0..n-1): if k<n/2: e_k ; else -e_{k-n/2}.
    half=n//2
    # only valid for n a power of 2
    assert (n & (n-1))==0, "char0 helper assumes n=2^mu"
    def vec(k):
        k%=n
        v=[0]*half
        if k<half: v[k]=1
        else: v[k-half]=-1
        return tuple(v)
    from collections import Counter
    dist=Counter({tuple([0]*half):1})
    for _ in range(r):
        nd=Counter()
        for v,c in dist.items():
            for k in range(n):
                vk=vec(k)
                nv=tuple(a+b for a,b in zip(v,vk))
                nd[nv]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def tangent_sum_charp(S, p, h_exp, hroot):
    """T_h = sum_{w in ker chi} phi(1-w) where ker chi = subgroup of index m,
       i.e. ker chi = mu_n (the n elements of S, the order-n subgroup), and
       phi = chi^h a character.  Here we take chi the order-n character?
       In the file: chi has order m = (p-1)/n? Let's match TangentSum file:
         T(phi) = sum_{x in ker chi} phi(1-x),  ker chi = order-(m-index) subgroup.
       For the prize Gauss-period house, ker chi = mu_n (order n).  phi = chi^h.
       We compute |T_h| for the order-n subgroup S and phi = a character of
       order dividing p-1, raised to power giving 'phi'.  We just sweep phi
       over all multiplicative characters chi_j (j=0..p-2) and report max_j |T|.
    """
    g = primitive_root(p)
    # discrete log table
    dlog = {}
    x=1
    for e in range(p-1):
        dlog[x]=e
        x=(x*g)%p
    import cmath
    best=0.0
    bestj=None
    vals=[]
    for j in range(1,p-1):  # nonprincipal characters chi_j(x)=exp(2pi i j dlog(x)/(p-1))
        T=0+0j
        for w in S:
            t=(1-w)%p
            if t==0:  # phi(0)=0
                continue
            T += cmath.exp(2j*math.pi*j*dlog[t]/(p-1))
        if abs(T)>best:
            best=abs(T); bestj=j
    return best,bestj

def find_proper_subgroup_primes(n, beta_lo=4, beta_hi=5, count=3):
    """primes p ~ n^beta with n | p-1 and p making mu_n a PROPER subgroup
       (n < p-1, always true here) and p large prime."""
    lo=int(n**beta_lo); hi=int(n**beta_hi)
    out=[]
    # search p = 1 + k*n prime in [lo,hi]
    import sympy
    k0 = max(2,(lo-1)//n)
    k=k0
    while len(out)<count and 1+k*n<=hi*4:
        p=1+k*n
        if sympy.isprime(p):
            out.append(p)
        k+=1
    return out

def main():
    try:
        import sympy
    except ImportError:
        print("need sympy"); sys.exit(1)
    for n in [8, 16, 32]:
        phi=euler_phi(n)
        primes=find_proper_subgroup_primes(n, count=2)
        for p in primes:
            S,h=subgroup(n,p)
            beta=math.log(p)/math.log(n)
            print(f"\n=== n={n} (phi={phi})  p={p}  (p~n^{beta:.2f}, proper subgroup) ===")
            # r_N: smallest r with (2r)^phi >= p
            rN=None
            for r in range(1,40):
                if (2*r)**phi >= p:
                    rN=r; break
            print(f"  norm threshold r_N (smallest r with (2r)^phi >= p): {rN}")
            # r_E: smallest r with E_r > E_r^char0
            rE=None
            for r in range(1,7):  # keep r small for cost (n^{2r} growth)
                if n**r > 4_000_000:  # cost guard on sumset
                    print(f"    [E_r: stop at r={r}, cost guard]")
                    break
                ec0=E_r_char0(S,p,r)
                ecp=E_r(S,p,r)
                mark = "  <-- DEFECT" if ecp!=ec0 else ""
                print(f"    r={r}: E_r^charp={ecp}  E_r^char0={ec0}{mark}")
                if ecp!=ec0 and rE is None:
                    rE=r
            print(f"  energy defect onset r_E: {rE}   (vs r_N={rN})")
    print("\n--- Tangent sum check (single scalar per prime; no r-index) ---")
    for n in [8,16]:
        primes=find_proper_subgroup_primes(n, count=1)
        for p in primes:
            S,h=subgroup(n,p)
            best,bestj=tangent_sum_charp(S,p,None,h)
            # char-0 / Jacobi-equidistributed prediction: |T_h| ~ sqrt(n) typically
            print(f"  n={n} p={p}: max_phi |T_h| = {best:.3f}   sqrt(n)={math.sqrt(n):.3f}   n={n}")

if __name__=="__main__":
    main()
