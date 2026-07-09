# Part 7: the "single-integer Rosetta stone" (C013): Res(Phi_n, g) = N(alpha)
#   = char-p defect threshold (F12) = ideal-SVP norm (F11) = additive-energy zero-detector (F5)
# Test: a u=1 BGK additive-energy collision in mu_n exists iff p | 2^n - 1 (the Mersenne obstruction)
#   AND that = prod of Fermat numbers F_0..F_{k-1} for n=2^k.
from collections import Counter
import itertools, math

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g

def fermat(j): return 2**(2**j)+1

# For n=2^k, Mersenne 2^n-1 = prod_{j<k} F_j.  Verify the u=1 obstruction primes.
print("=== n=2^k: bad-char primes for u=1 cell = prime factors of F_0..F_{k-1} ===")
for k in range(1,6):
    n=2**k
    mers=2**n-1
    prod=math.prod(fermat(j) for j in range(k))
    print(f"  k={k} n={n}: 2^n-1={mers}  prod F_j={prod}  match={mers==prod}  Fermats={[fermat(j) for j in range(k)]}")

# Now: does p | 2^n-1  <=>  the smooth subgroup mu_n over F_p has the u=1 energy collision
#   (i.e. -2 in mu_n, equivalently 2 in mu_n since -1 in mu_n for n even)?
# Test small primes dividing Fermat numbers vs whether 2 has order dividing n in F_p*.
print("\n=== p | F_j (some j<k)  <=>  2^(2^k) = 1 in F_p  (order of 2 divides n) ===")
for p in [3,5,17,257,7,11,13,97,193,641]:  # 641 | F_5
    for k in [3,4,5]:
        n=2**k
        ord2_div_n = (pow(2,n,p)==1)
        fermat_dvd = any(fermat(j)%p==0 for j in range(k))
        # they should match
        flag = "OK" if ord2_div_n==fermat_dvd else "XX"
        if k==5 or ord2_div_n:
            print(f"  p={p:>4} k={k} n={n:>3}: 2^n=1 mod p? {ord2_div_n}  p|some F_j? {fermat_dvd}  {flag}")

# Cross-domain: the SAME Res(Phi_n,g)=N(alpha) integer as a NORM. For alpha=sum of sparse
# roots of unity, N(alpha)=prod over Galois conj. p|N(alpha) <=> alpha has a root mod p
# <=> energy collision mod p. Demonstrate: alpha = 1 + zeta (zeta primitive n-th root),
# N(alpha) = Phi_n evaluated... = resultant.
print("\n=== single-integer norm: alpha=1+2 (the u=1 sum), 'N'=2^n-1, p|N <=> collision ===")
for k in [3,4,5]:
    n=2**k
    print(f"  n={n}: the u=1 detector integer = 2^n-1 = {2**n-1}, its odd prime factors are the bad chars")
