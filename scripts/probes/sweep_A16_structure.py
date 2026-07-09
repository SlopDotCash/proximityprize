"""
A16 structure-finder: characterize the orbit reps EXACTLY to design the Lean proof.

From the first probe the n/4-1 orbits each have a representative of the form
  S_j (exponents) = {0, j, 2j, n/2 + j}   for j = 1 .. n/4 - 1.
We verify:
  (a) For every j in 1..n/4-1, the 4-subset {zeta^0, zeta^j, zeta^{2j}, zeta^{n/2+j}} has e_2 = 0 and e_1 != 0.
  (b) These represent DISTINCT orbits (no zeta^t maps S_i multiset onto S_j for i != j).
  (c) j = n/4 gives the EXCLUDED mu_4-coset (e_1 = 0): {0, n/4, n/2, 3n/4}.
  (d) Every e_2=0, e_1!=0 4-subset is in exactly one of these orbits (already shown by orbit count).

WHY e_2 = 0 for S_j = {1, w, w^2, -w} where w = zeta^j (note zeta^{n/2}=-1 so zeta^{n/2+j} = -w):
  roots = 1, w, w^2, -w.
  e_2 = sum of pairwise products
      = 1*w + 1*w^2 + 1*(-w) + w*w^2 + w*(-w) + w^2*(-w)
      = w + w^2 - w + w^3 - w^2 - w^3
      = 0.   <-- exact, identically zero as a POLYNOMIAL in w.  No cyclotomic reduction needed!
  e_1 = 1 + w + w^2 - w = 1 + w^2.   != 0 iff w^2 != -1 iff zeta^{2j} != zeta^{n/2}
      iff 2j != n/2 mod n iff j != n/4 mod n/2.  For j in 1..n/4-1 this holds.

  Distinctness of the four roots {1, w, w^2, -w}: need 1,w,w^2,-w pairwise distinct.
  w=zeta^j, j in 1..n/4-1 so w is a primitive-ish root; check below.
"""
import itertools

def roots_of_Sj(n, j):
    # exponents (0, j, 2j mod n, n/2 + j)
    return tuple(sorted([0 % n, j % n, (2*j) % n, (n//2 + j) % n]))

def exact_e2_zero(exps, n):
    half = n // 2
    coeff = [0]*n
    for i,k in itertools.combinations(range(4),2):
        coeff[(exps[i]+exps[k])%n]+=1
    red=[0]*half
    for jj in range(n):
        if jj<half: red[jj]+=coeff[jj]
        else: red[jj-half]-=coeff[jj]
    return all(c==0 for c in red)

def exact_e1_zero(exps, n):
    half=n//2
    coeff=[0]*n
    for e in exps: coeff[e%n]+=1
    red=[0]*half
    for jj in range(n):
        if jj<half: red[jj]+=coeff[jj]
        else: red[jj-half]-=coeff[jj]
    return all(c==0 for c in red)

def orbit_key(exps, n):
    best=None
    for t in range(n):
        s=tuple(sorted((e+t)%n for e in exps))
        if best is None or s<best: best=s
    return best

for n in [8,16,32,64,128]:
    print(f"=== n={n} ===")
    half=n//2
    keys=set()
    all_ok=True
    distinct_ok=True
    for j in range(1, n//4):
        exps=roots_of_Sj(n,j)
        # all four exponents must be distinct (it's a 4-SUBSET)
        if len(set(exps))!=4:
            print(f"  j={j}: NOT 4 distinct roots! exps={exps}")
            distinct_ok=False
            continue
        e2=exact_e2_zero(exps,n)
        e1nz=not exact_e1_zero(exps,n)
        if not (e2 and e1nz):
            print(f"  j={j}: e2zero={e2} e1nonzero={e1nz} FAIL exps={exps}")
            all_ok=False
        keys.add(orbit_key(exps,n))
    # j = n/4 should be the excluded mu_4 coset
    jx=n//4
    exps_x=roots_of_Sj(n,jx)
    print(f"  j=n/4={jx}: exps={exps_x}  e2zero={exact_e2_zero(exps_x,n)}  e1zero(excluded)={exact_e1_zero(exps_x,n)}")
    print(f"  family j=1..n/4-1: all (e2=0,e1!=0,4distinct)? {all_ok and distinct_ok}")
    print(f"  # distinct orbits among the family = {len(keys)}   (predicted n/4-1 = {n//4-1})  MATCH={len(keys)==n//4-1}")
    print()
