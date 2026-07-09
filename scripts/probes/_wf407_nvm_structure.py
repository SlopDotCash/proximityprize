"""
Characterize the SINGULAR distinct-degree minors over mu_n at 2-power index.
This is the genuine obstruction: even an ordinary [z_i^{d_j}] determinant
with distinct points z_i in mu_n and distinct degrees d_j can VANISH because
the points are structured roots of unity. We identify the pattern.

det[z_i^{d_j}] = generalized Vandermonde = (sum over perms) and factors as
the ordinary Vandermonde times a Schur polynomial s_lambda(z) where lambda is
the partition (d_j - (j-1)). It vanishes iff the Schur polynomial vanishes on
the chosen subgroup points. Over a multiplicative subgroup, Schur polys can
vanish (power-sum / root-of-unity coincidences). We test the dependence on n.
"""
import itertools, math
def is_prime(x):
    if x<2:return False
    i=2
    while i*i<=x:
        if x%i==0:return False
        i+=1
    return True
def primitive_root(p):
    if p==2:return 1
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

# For n=8, p=73: enumerate singular distinct-degree minors and find what
# distinguishes them. Hypothesis: vanishes when the degree set d_j and point
# set hit a vanishing-sum-of-roots-of-unity (Lam-Leung) relation: degrees
# differ by multiples of n/gcd, points form a coset of a subgroup of mu_n.
n=8
p=73
g=primitive_root(p);m=(p-1)//n
H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
# H = mu_8: indices 0..7, H[j] = zeta^j where zeta is a primitive 8th root
print(f"mu_{n} over F_{p}: H = {H}")
print(f"As powers of generator of mu_n (zeta=H[1]={H[1]}): H[j]=zeta^j")
# log table within mu_n
zeta=H[1]
logt={pow(zeta,j,p):j for j in range(n)}
r=3
sing_patterns=[]
for degs in itertools.combinations(range(n), r):
    for pts in itertools.combinations(range(n), r):  # indices into H
        ptvals=[H[j] for j in pts]
        M=[[pow(x,d,p) for d in degs] for x in ptvals]
        if det(M,p)==0:
            sing_patterns.append((degs,pts))
print(f"\nTotal singular distinct-degree 3x3 minors: {len(sing_patterns)}")
# analyze: for each singular minor, degrees mod n and point-index differences
from collections import Counter
deg_mod = Counter()
pt_diff = Counter()
for degs,pts in sing_patterns[:200]:
    deg_mod[tuple(d % n for d in degs)] += 1
    # differences of point indices mod n
    diffs=tuple(sorted((pts[j]-pts[0])%n for j in range(len(pts))))
    pt_diff[diffs]+=1
print("\nMost common (degrees mod n) among singular minors:")
for k,v in deg_mod.most_common(8): print(f"   degs mod {n} = {k}: {v}")
print("\nMost common point-index-difference patterns (mod n):")
for k,v in pt_diff.most_common(8): print(f"   pt diffs = {k}: {v}")

# Confirm: are the singular ones exactly where degrees are congruent mod a
# divisor matching point structure? Check the simplest Lam-Leung instance:
# 3 points forming {a, a+n/2-coset...}. Print a few explicit singular minors.
print("\nExample singular minors (degree set, point indices in mu_8):")
for degs,pts in sing_patterns[:6]:
    print(f"   degrees={degs}, point indices={pts}")

# Compare with PRIME n: should be ZERO singular (Schur poly nonvanishing on
# prime-order roots of unity due to no nontrivial vanishing sums).
print("\n--- Control: prime n, distinct-degree minors (expect 0 singular) ---")
for nn in [3,5,7,11]:
    pp=None
    for q in range(101,5000):
        if is_prime(q) and (q-1)%nn==0:pp=q;break
    gg=primitive_root(pp);mm=(pp-1)//nn
    HH=[pow(gg,(mm*j)%(pp-1),pp) for j in range(nn)]
    rr=min(3,nn)
    s=0;t=0
    for degs in itertools.combinations(range(nn), rr):
        for pts in itertools.combinations(HH, rr):
            M=[[pow(x,d,pp) for d in degs] for x in pts]
            t+=1
            if det(M,pp)==0:s+=1
    print(f"   n={nn} (prime) p={pp}: {s}/{t} singular")
