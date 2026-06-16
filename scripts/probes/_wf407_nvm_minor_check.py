"""
R3 / NVM uncertainty-principle probe for #407.

CLAIM under test (route hypothesis from prompt):
  The 'LovettPrimitiveStep' residual of GM-MDS/Lovett, in the SPECIFIC-DOMAIN
  (subgroup mu_n) version, is the nonvanishing-minors (NVM) property of the
  compressed Fourier matrix of H = mu_n: a 'repeated-degree generalized
  Vandermonde' nonsingularity, characterized via Gauss sums (Chebotarev on
  roots of unity). Index 2,3 'solved', index>=4 / 2-power 'open'.

We test TWO concrete things over actual prime fields F_p:

(A) NVM / generalized-Vandermonde nonsingularity for H = mu_n at INDEX m = (p-1)/n
    in {2,3,4} and 2-power. The compressed Fourier matrix of a subgroup H of
    F_p^* (size n, index m): rows indexed by characters constant on cosets =
    H-periodic, i.e. the m Gauss periods. The relevant minors are the
    generalized-Vandermonde determinants on the period values.

(B) Whether the NVM/algebraic fact, EVEN IF TRUE for all index, says ANYTHING
    about the prize floor B = max_b |eta_b|. (Spoiler test: NVM is a
    nonvanishing = NONZERO statement; B is an archimedean SIZE statement.
    A determinant being nonzero gives no upper bound on |eta_b|.)
"""
import cmath, math, itertools

def primes_with_index(m, want=6, nmin=2):
    """Find primes p with (p-1) = m*n, n>=nmin, several values."""
    out=[]
    n=nmin
    while len(out)<want and n < 4000:
        p = m*n+1
        if is_prime(p):
            out.append((p,n))
        n+=1
    return out

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def primitive_root(p):
    if p==2: return 1
    fact=[]
    phi=p-1; x=phi; d=2
    while d*d<=x:
        if x%d==0:
            fact.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fact.append(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fact):
            return g
    return None

def gauss_periods(p, n):
    """eta_b for b in F_p^*, eta_b = sum_{x in mu_n} e_p(b x). Returns dict and B."""
    g = primitive_root(p)
    m = (p-1)//n
    # mu_n = { g^(m*j) : j=0..n-1 }
    H = [pow(g, (m*j) % (p-1), p) for j in range(n)]
    w = 2j*math.pi/p
    etas = {}
    for b in range(1,p):
        s = sum(cmath.exp(w*((b*h)%p)) for h in H)
        etas[b] = s
    B = max(abs(v) for v in etas.values())
    return etas, B, H, g, m

# ---------- (A) NVM / generalized Vandermonde nonsingularity ----------
# The "compressed Fourier matrix" of H: the m distinct Gauss-period values
# eta_{c} for c ranging over coset reps of mu_n in F_p^* (m of them).
# Generalized Vandermonde minor on r distinct period-VALUES z_1..z_r with
# degree multiset D (the "repeated-degree" = degrees can repeat): det of
# matrix [ z_i^{d_j} ]. NVM <=> this is nonzero for the relevant patterns.
# For DISTINCT degrees d_j and distinct z_i -> ordinary Vandermonde-type,
# nonzero iff z_i distinct (in-tree linearIndependent_of_injOn_natDegree).
# The HARD case = repeated degrees (Lovett's genuine content). We test the
# subgroup-specific minors numerically.

def det(M, p):
    """Determinant of integer matrix mod p (Gaussian elimination)."""
    M=[row[:] for row in M]; n=len(M); d=1
    for col in range(n):
        piv=None
        for r in range(col,n):
            if M[r][col]%p!=0: piv=r; break
        if piv is None: return 0
        if piv!=col:
            M[col],M[piv]=M[piv],M[col]; d=(-d)%p
        inv=pow(M[col][col],p-2,p)
        d=(d*M[col][col])%p
        for r in range(col+1,n):
            f=(M[r][col]*inv)%p
            for c in range(col,n):
                M[r][c]=(M[r][c]-f*M[col][c])%p
    return d%p

print("="*70)
print("(A) Subgroup compressed-Fourier / generalized-Vandermonde minors")
print("    over the COSET-REP period values, index m = 2,3,4, 8 (2-power)")
print("="*70)
for m in [2,3,4,8]:
    print(f"\n--- index m={m} ---")
    for p,n in primes_with_index(m, want=4, nmin=2):
        g = primitive_root(p)
        # coset reps of mu_n: g^0, g^1, ..., g^{m-1}
        reps = [pow(g, i, p) for i in range(m)]
        # Build the m x m subgroup-period Vandermonde on reps with degrees 0..m-1
        # (this is the 'compressed Fourier matrix' core minor)
        V = [[pow(reps[i], j, p) for j in range(m)] for i in range(m)]
        dV = det(V, p)
        # repeated-degree generalized vandermonde: degrees {0,0,1,...} i.e.
        # replace last column degree m-1 by a repeat of degree 0 (constant col)
        # -> this is SINGULAR by construction (two equal columns) - sanity.
        Vrep = [row[:] for row in V]
        for i in range(m): Vrep[i][m-1]=Vrep[i][0]
        dVrep = det(Vrep, p)
        print(f"  p={p:5d} n={n:4d}: det(Vandermonde reps)={dV:4d} (nonzero={dV!=0}), "
              f"det(forced-repeat-col)={dVrep} (must be 0)")
