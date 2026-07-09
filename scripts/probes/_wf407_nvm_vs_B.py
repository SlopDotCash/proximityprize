"""
R3 probe part (B): does NVM/algebraic nonsingularity bound the prize floor B?
And: the REAL Lovett-hard content = repeated-degree generalized Vandermonde
over the subgroup, tested via Lam-Leung / Chebotarev vanishing-sum theory at
2-power index.
"""
import cmath, math

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def primitive_root(p):
    if p==2: return 1
    fact=[]; x=p-1; d=2
    while d*d<=x:
        if x%d==0:
            fact.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fact.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fact): return g

def gauss_periods(p,n):
    g=primitive_root(p); m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    w=2j*math.pi/p
    B=0.0
    for b in range(1,p):
        s=abs(sum(cmath.exp(w*((b*h)%p)) for h in H))
        if s>B: B=s
    return B,m

print("="*72)
print("(B1) NVM is a NONZERO statement. Test: does subgroup-Vandermonde")
print("     nonsingularity correlate AT ALL with the size B? (it must NOT,")
print("     if the verdict 'algebra controls non-archimedean only' holds.)")
print("="*72)
print(f"{'p':>6} {'n':>5} {'m':>4} {'B':>9} {'sqrt(n ln m)':>13} {'R=B/that':>9}")
# 2-power index family, growing n
data=[]
for n in [2,4,8,16,32]:
    # find a prime with index a power of 2 and this n if possible; else nearest
    for m in [2,4,8,16,32,64,128,256]:
        p=m*n+1
        if is_prime(p):
            B,mm=gauss_periods(p,n)
            denom=math.sqrt(n*math.log(max(mm,2)))
            R=B/denom if denom>0 else float('nan')
            print(f"{p:6d} {n:5d} {mm:4d} {B:9.4f} {denom:13.4f} {R:9.4f}")
            data.append((p,n,mm,B,R))
            break

print()
print("="*72)
print("(B2) Repeated-degree generalized Vandermonde over mu_n at 2-power index")
print("     = the GENUINE Lovett-hard NVM. Lam-Leung: a vanishing sum of")
print("     N n-th roots of unity (n=2^a) has N in <0,2,4,...> (2*Z_{>=0}).")
print("     The 'repeated degree' minor vanishes iff a structured root-of-unity")
print("     relation exists. Test how OFTEN repeated-degree minors vanish at")
print("     2-power index vs odd/prime index (the worst-case claim).")
print("="*72)

def det(M,p):
    M=[r[:] for r in M]; n=len(M); d=1
    for c in range(n):
        piv=None
        for r in range(c,n):
            if M[r][c]%p: piv=r;break
        if piv is None: return 0
        if piv!=c: M[c],M[piv]=M[piv],M[c]; d=(-d)%p
        inv=pow(M[c][c],p-2,p); d=(d*M[c][c])%p
        for r in range(c+1,n):
            f=(M[r][c]*inv)%p
            for cc in range(c,n): M[r][cc]=(M[r][cc]-f*M[c][cc])%p
    return d%p

import itertools
def count_repeated_degree_singular(p, n, r, max_deg):
    """Among r-subsets of mu_n and degree-multisets of size r (with repeats)
    drawn from 0..max_deg, how many generalized-Vandermonde minors VANISH?
    Returns (total, singular)."""
    g=primitive_root(p); m=(p-1)//n
    H=[pow(g,(m*j)%(p-1),p) for j in range(n)]
    tot=0; sing=0
    # degree multisets (with repetition) of size r from 0..max_deg
    for degs in itertools.combinations_with_replacement(range(max_deg+1), r):
        for pts in itertools.combinations(H, r):
            M=[[pow(x,d,p) for d in degs] for x in pts]
            tot+=1
            if det(M,p)==0: sing+=1
    return tot,sing

print(f"{'p':>6} {'n':>5} {'m':>5} {'r':>3} {'singular/total minors':>24} {'frac':>8}")
# Compare a 2-power n vs a comparable odd/prime n at similar size, with REPEATED degrees allowed
cases=[(2,'2pow'),(4,'2pow'),(8,'2pow'),(3,'odd'),(5,'prime'),(9,'oddpow')]
for n,lab in cases:
    # pick smallest prime p>~50 with this n dividing p-1
    found=None
    for p in range(53,4000):
        if is_prime(p) and (p-1)%n==0:
            found=p; break
    if not found: continue
    r=min(3,n)
    md=min(3, n-1) if n>1 else 1
    if md<1: md=1
    tot,sing=count_repeated_degree_singular(found,n,r,md)
    print(f"{found:6d} {n:5d} {(found-1)//n:5d} {r:3d} {sing:10d}/{tot:<13d} {sing/tot:8.4f}  [{lab}]")
