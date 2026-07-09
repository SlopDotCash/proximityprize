"""
R3 CRUX probe: the NVM property at 2-power index, refined.

The NVM (nonvanishing-minors) residual 'LovettPrimitiveStep' for a SUBGROUP
domain H = mu_n is the statement: every generalized-Vandermonde minor
det[ z_i^{d_j} ] with the z_i in mu_n DISTINCT and the column degree multiset
{d_j} a genuine (column-distinct) pattern arising from a V*(k) system is
NONZERO. The hard case (Lovett) is when degrees REPEAT across blocks; the
nonsingularity there is governed by whether a structured vanishing sum of
roots of unity exists -- Chebotarev/Lam-Leung territory.

KEY DISTINCTION we test:
 - For GENERIC evaluation points (the in-tree MvPolynomial GM-MDS), the minor
   is a nonzero polynomial, so nonsingular at generic points -> in-tree
   LovettPrimitiveStep is the right object and the prize's mu_n is just ONE
   specialization. The danger: mu_n is NON-generic (highly structured), so the
   minor COULD vanish on it even though it's a nonzero polynomial.
 - So the real R3 question: does the GM-MDS minor (nonzero as a polynomial)
   actually NONVANISH at the special point set mu_n? If it can vanish, the
   in-tree symbolic GM-MDS does NOT transfer to the prize subgroup.

We test: for the actual subgroup mu_n, do the relevant minors vanish?
"""
import itertools, math

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def primitive_root(p):
    if p==2: return 1
    fact=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fact.append(d)
            while x%d==0:x//=d
        d+=1
    if x>1:fact.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fact):return g
def det(M,p):
    M=[r[:] for r in M];n=len(M);d=1
    for c in range(n):
        piv=None
        for r in range(c,n):
            if M[r][c]%p:piv=r;break
        if piv is None:return 0
        if piv!=c:M[c],M[piv]=M[piv],M[c];d=(-d)%p
        inv=pow(M[c][c],p-2,p);d=(d*M[c][c])%p
        for r in range(c+1,n):
            f=(M[r][c]*inv)%p
            for cc in range(c,n):M[r][cc]=(M[r][cc]-f*M[c][cc])%p
    return d%p

print("="*72)
print("CRUX: Does an ORDINARY generalized-Vandermonde minor (DISTINCT degrees,")
print("DISTINCT points in mu_n) ever vanish? (these are the in-tree distinct-")
print("degree case -> should NEVER vanish; confirms in-tree theorem on mu_n.)")
print("="*72)
bad=0;tot=0
for n,lab in [(2,'2pow'),(4,'2pow'),(8,'2pow'),(3,'odd'),(5,'prime'),(16,'2pow')]:
    p=None
    for q in range(53,8000):
        if is_prime(q) and (q-1)%n==0:p=q;break
    g=primitive_root(p);m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    r=min(3,n)
    local_bad=0;local=0
    # DISTINCT degrees (strictly increasing) from 0..n-1
    for degs in itertools.combinations(range(n), r):
        for pts in itertools.combinations(H, r):
            M=[[pow(x,d,p) for d in degs] for x in pts]
            local+=1
            if det(M,p)==0:local_bad+=1
    print(f"  n={n:3d} [{lab:5s}] p={p:5d}: distinct-degree minors {local_bad}/{local} singular")
    bad+=local_bad;tot+=local
print(f"  TOTAL distinct-degree singular: {bad}/{tot}")

print()
print("="*72)
print("CRUX2: REPEATED-degree minors with DISTINCT COLUMNS (genuine general.")
print("Vandermonde, the Lovett-hard case). A column pattern: r points, r")
print("columns where column degrees come from a multiset that REPEATS a value")
print("but we keep columns distinct by pairing degree with a different point-")
print("subset structure. Concretely: test det[ z_i^{d_j} ] where {d_j} has a")
print("repeat -> these columns ARE equal -> det=0 TRIVIALLY. So pure repeated")
print("degree on the SAME point set is always singular. The Lovett structure")
print("avoids this via the BLOCK structure (different vanishing factors).")
print("Conclusion test below.")
print("="*72)

# The genuine Lovett minor is NOT [z_i^d_j] with repeated d_j on same points.
# It is the coefficient matrix of the union family P(k,V): rows = polynomials
# pVanish(V_i)*X^e, columns = coeffs 0..k-1. Two members can have the SAME
# natDegree (|V_i|+e) when blocks overlap -> that's the repeated-degree case.
# Test: build P(k,V) for a small primitive V*(k) over evaluation set = mu_n
# (instead of generic), and check rank.
def pvanish_coeffs(roots, p):
    # monic poly with given roots (mod p): returns coeff list low->high
    c=[1]
    for r in roots:
        nc=[0]*(len(c)+1)
        for i,ci in enumerate(c):
            nc[i]=(nc[i]+(-r*ci))%p
            nc[i+1]=(nc[i+1]+ci)%p
        c=nc
    return c

print("Building union family P(k,V) with evaluation points = mu_n,")
print("checking if the coefficient matrix (over F_p) is full rank:")
for n,lab in [(4,'2pow'),(8,'2pow'),(3,'odd'),(16,'2pow')]:
    p=None
    for q in range(101,20000):
        if is_prime(q) and (q-1)%n==0:p=q;break
    g=primitive_root(p);m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    # simple V*(k): k=3, two vectors each picking distinct roots from H
    k=3
    # V_1 vanishes at H[0]; V_2 vanishes at H[1]; |V_i|=1 -> e in 0..k-2 (=0,1)
    # union members: pVanish({H[0]})*X^e (e=0,1), pVanish({H[1]})*X^e (e=0,1)
    members=[]
    for root in [H[0],H[1]]:
        base=pvanish_coeffs([root],p)  # degree 1
        for e in range(k-1):  # e=0,1
            coeffs=[0]*e+base  # multiply by X^e
            coeffs=coeffs[:k]+[0]*(k-len(coeffs))
            coeffs=coeffs[:k]
            members.append(coeffs)
    # coefficient matrix (members x k), check rank over F_p
    M=[row[:] for row in members]
    rank=0;Mr=[r[:] for r in M];rows=len(Mr);cols=k;pr=0
    for c in range(cols):
        piv=None
        for r in range(pr,rows):
            if Mr[r][c]%p:piv=r;break
        if piv is None:continue
        Mr[pr],Mr[piv]=Mr[piv],Mr[pr]
        inv=pow(Mr[pr][c],p-2,p)
        for r in range(rows):
            if r!=pr and Mr[r][c]%p:
                f=(Mr[r][c]*inv)%p
                for cc in range(cols):Mr[r][cc]=(Mr[r][cc]-f*Mr[pr][cc])%p
        pr+=1;rank+=1
    print(f"  n={n:3d} [{lab:5s}] p={p:5d}: union family size={len(members)}, "
          f"rank={rank} (indep iff rank={len(members)})")
