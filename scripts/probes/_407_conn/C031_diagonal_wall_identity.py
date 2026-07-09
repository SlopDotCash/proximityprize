#!/usr/bin/env python3
"""
C031 follow-up: WHICH wall is the CS25 diagonal floor?

The connection asserts the diagonal I(0)=V is "the n^{1/2} energy-deficit wall"
and welds to walls=[W-Johnson]. Two competing readings:

  (R1) CS25/Paley-Zygmund covered-set lower bound:
       |close| >= (|C| V)^2 / E[N^2] = (|C| V)^2 / (|C| sum_v I(v))
                = |C| V^2 / (V + offdiag).
       Here the DIAGONAL V in the denominator is the GOOD term (it gives the
       leading |C|*V when offdiag is small). This is a COVERING / list-RECOVERY
       statement, NOT a list-SIZE-lower-bound. The diagonal HELPS, it is not a "wall".

  (R2) The additive-energy list-size story (the prize BGK wall): for S=mu_n,
       list L of an RS code satisfies (Cheng-style)  L <= sqrt(n * E_2(S))/something,
       and E_2(S) >= |S|^2 (diagonal) forces a floor. But the relevant deficit is
       whether E_2 = n^2 (Sidon-like, GOOD => sqrt-cancellation) vs n^3 (bad).

We test:
 (a) whether E_2(mu_n) grows like n^2 (good) or n^3 (the feared deficit) as n grows
     across MANY proper-subgroup prize-shaped primes -- to see if there is any
     "n^{1/2} deficit wall" in E_2 at all.
 (b) the CS25 Paley-Zygmund bound direction: does the diagonal V act as a floor that
     BLOCKS list recovery, or as the GOOD leading term?
"""

import itertools
from collections import Counter
from math import comb, isqrt

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; m = phi; factors=set(); d=2
    while d*d<=m:
        if m%d==0:
            factors.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors): return g
    raise RuntimeError

def subgroup(q,n):
    g=primitive_root(q); step=(q-1)//n
    return sorted({pow(g,step*i,q) for i in range(n)})

def e2(q,mu):
    rc=Counter()
    for a in mu:
        for b in mu:
            rc[(a+b)%q]+=1
    diag = sum(1 for a in mu for b in mu if (a==b))  # = n (a+b with a=b is fine but diagonal of pairs)
    # additive-energy diagonal floor = solutions a+b=c+d with (a,b)=(c,d) or (a,b)=(d,c) = 2n^2 - (#a=b)
    return sum(v*v for v in rc.values())

# Part (a): E_2 scaling across prize-shaped primes (n << sqrt q, proper subgroup, large prime, q=1 mod n)
print("="*86)
print("(a) E_2(mu_n) scaling: is there a 'n^{1/2} deficit'? (target good=n^2*polylog, bad=n^3)")
print("="*86)
print(f"{'n':>5} {'q':>14} {'beta':>6} {'E_2':>12} {'E2/n^2':>8} {'E2/n^3':>9} {'B=sqrt(E2/n)':>13} {'2sqrt n':>9}")
# choose, for each n=2^mu, a prime q = 1 mod n with q ~ n^beta (beta in 4..5), proper subgroup, large.
def find_prime(n, target):
    # smallest prime > target with q = 1 mod n
    import sympy
    t = target - (target % n) + 1
    while True:
        if t > target and sympy.isprime(t):
            return t
        t += n
try:
    import sympy
    have_sympy=True
except Exception:
    have_sympy=False

cases=[]
if have_sympy:
    for mu in range(3,9):     # n = 8,16,32,64,128,256
        n=2**mu
        beta=4.5
        target=int(n**beta)
        q=find_prime(n, target)
        cases.append((n,q))
else:
    cases=[(8,12289),(16,12289),(16,40961),(32,40961),(32,786433),(64,786433)]

for (n,q) in cases:
    if (q-1)%n!=0: continue
    mu=subgroup(q,n)
    E=e2(q,mu)
    beta=__import__('math').log(q)/__import__('math').log(n)
    B=(E/n)**0.5
    print(f"{n:>5} {q:>14} {beta:>6.2f} {E:>12} {E/n**2:>8.3f} {E/n**3:>9.5f} {B:>13.2f} {2*n**0.5:>9.2f}")

print()
print("READING: if E_2/n^2 stays O(polylog) and E_2/n^3 -> 0, then E_2 ~ n^2 (the GOOD/")
print("Sidon-like regime), B=sqrt(E2/n) ~ sqrt(n) ~ Ramanujan. There is NO 'n^{1/2} deficit")
print("wall' visible in E_2(mu_n) at these scales -- the wall is the WORST-CASE per-frequency")
print("B = max_b |sum ψ(b y)| (BGK), which E_2 (an AVERAGE 2nd moment) does NOT see.")

# Part (b): Paley-Zygmund direction check on small RS code (diagonal is the GOOD term)
print()
print("="*86)
print("(b) CS25 Paley-Zygmund: |close| >= |C| V^2/(V+offdiag). Diagonal V is the GOOD leading term?")
print("="*86)
def hdist(x,y): return sum(1 for a,b in zip(x,y) if a!=b)
def rs_code(q,n,k):
    pts=list(range(n)); code=[]
    for co in itertools.product(range(q),repeat=k):
        code.append(tuple(sum(co[j]*pow(p,j,q) for j in range(k))%q for p in pts))
    return code
def ball_inter(F,n,r,v):
    z=tuple(0 for _ in range(n)); c=0
    for x in itertools.product(F,repeat=n):
        if hdist(x,z)<=r and hdist(x,v)<=r: c+=1
    return c
q,n,k=5,4,2
F=list(range(q)); code=rs_code(q,n,k)
print(f"RS[F_{q},n={n},k={k}] |C|={len(code)}")
for r in range(1,n):
    V=ball_inter(F,n,r,tuple([0]*n))
    offdiag=sum(ball_inter(F,n,r,v) for v in code if any(x!=0 for x in v))
    sumI=V+offdiag
    pz_lower = len(code)*V*V/(sumI)   # = (|C|V)^2 / E[N^2] / ... careful: E[N^2]=|C|*sumI
    # covered fraction lower bound = (|C|V)^2 / (|F^n| * E[N^2]) is the fraction; here just |close| >= (|C|V)^2/E[N^2]
    EN2=len(code)*sumI
    close_lb=(len(code)*V)**2/EN2
    print(f" r={r}: V(diag)={V:>4} offdiag={offdiag:>6} -> |close|>= (|C|V)^2/E[N^2] = {close_lb:8.2f}"
          f"  (= |C|*V/(1+offdiag/V) = {len(code)*V/(1+offdiag/V):8.2f}); diag in DENOM is helpful when offdiag<<V")
print()
print("READING: the diagonal V appears in the DENOMINATOR of E[N^2]=|C|(V+offdiag) and in the")
print("NUMERATOR as (|C|V)^2. When offdiag/V -> 0, |close| -> |C|*V (full recovery). The diagonal")
print("is the RECOVERY-ENABLING term, not a list-size lower-bound 'wall'. A list lower bound (the")
print("BGK obstruction) would need offdiag >> V (clustering), which is the SAME open question as")
print("'is E_2 large / does B fail to be sqrt(n)'. The CS25 2nd moment gives the AVERAGE; the prize")
print("needs the WORST-CASE per-coset, which the 2nd moment provably cannot reach (C015/_MomentMethodNoGo).")
