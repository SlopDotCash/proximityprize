"""
C097 follow-up: WHAT saving does the per-character bridge need, and can Stepanov give it?

The bridge collision_le_of_relative_bound gives  M2 <= C^2/|A| + eps*C^2  with C=C(n,a),
|A|=q^2.  Anti-concentration (the prize-favourable regime) needs M2 ~ C^2/|A| = C^2/q^2,
i.e. it needs eps <~ 1/q^2 (so the eps*C^2 term doesn't dominate the C^2/|A| floor).  More
charitably, "M2 is anti-concentrated / Johnson holds" needs eps at most ~ 1/q (a sqrt(q)
saving per the connection's own 'sqrt(q)-strength' language), i.e.
        ||T_psi||^2 <~ C(n,a)^2 / q     for ALL psi != 0.

We measure the ACTUAL worst-case saving  S_psi = C(n,a)^2 / max_psi||T_psi||^2  and compare
to the target q (sqrt(q)-strength).  If S_psi is O(1) (not ~q), no Stepanov/Weil per-character
bound of sqrt(q) strength exists, because the truth itself has ||T_psi||^2 ~ C^2 (no cancellation):
the elementary-symmetric e_a does NOT inherit per-element sqrt-cancellation on a thin subgroup.

Decisive sub-test: the worst psi is b=(0,b2) (pure quadratic-moment char), chi(x)=psi(b2 x^2).
On the THIN subgroup mu_n, x^2 ranges over mu_n^2 (a subgroup of index gcd), so chi is NEARLY
CONSTANT on cosets -> e_a barely cancels.  This is the BGK/Paley wall, NOT a Johnson-level
quantity Stepanov can reach.
"""
import math, itertools
import numpy as np
from math import comb

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def primitive_root(q):
    phi=q-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,phi//p,q)!=1 for p in fac): return g
def find_primes(n,blo,bhi,want):
    lo=int(n**blo); hi=int(n**bhi); out=[]; q=lo-(lo%n)+1
    if q<lo: q+=n
    while q<=hi and len(out)<want:
        if isprime(q) and (q-1)%n==0 and (q-1)//n>1: out.append(q)
        q+=n
    return out
def subgroup(n,q):
    g=primitive_root(q); h=pow(g,(q-1)//n,q); return [pow(h,i,q) for i in range(n)]

def worst(elts,a,q,bsweep=800,rand=800,seed=2):
    s1=[];s2=[]
    for S in itertools.combinations(elts,a):
        s1.append(sum(S)%q); s2.append(sum((x*x)%q for x in S)%q)
    s1=np.array(s1,np.int64); s2=np.array(s2,np.int64); N=len(s1); C2=N*N
    rng=np.random.default_rng(seed); cands=set()
    for b1 in range(1,min(q,bsweep)): cands.add((b1,0))
    for b2 in range(1,min(q,bsweep)): cands.add((0,b2))
    for _ in range(rand):
        b=(int(rng.integers(q)),int(rng.integers(q)))
        if b!=(0,0): cands.add(b)
    tp=2*math.pi/q; best=0.0; bb=None
    for (b1,b2) in cands:
        ang=tp*((b1*s1+b2*s2)%q); T=np.cos(ang).sum()+1j*np.sin(ang).sum()
        v=T.real*T.real+T.imag*T.imag
        if v>best: best=v; bb=(b1,b2)
    return best,C2,N,bb

print("="*84,flush=True)
print("C097: actual per-character SAVING S = C(n,a)^2 / max||T_psi||^2  vs needed ~q",flush=True)
print("="*84,flush=True)
for n in [8,16]:
    for q in find_primes(n,4.0,5.0,2):
        elts=subgroup(n,q)
        for a in sorted(set([2,n//2])):
            if comb(n,a)>13000:
                pass
            best,C2,N,bb=worst(elts,a,q)
            S=C2/best
            # quadratic-moment range: how many distinct values does x^2 take on mu_n?
            sq=set((x*x)%q for x in elts)
            print(f"n={n} q={q} a={a}: saving S=C^2/max||T||^2={S:.3f}   "
                  f"(sqrt(q)-strength target S~q={q})   worst b={bb}   "
                  f"#distinct x^2 on mu_n={len(sq)} (of n={n})",flush=True)
print("\nVERDICT SIGNAL: if S ~ O(1) (not ~q), the per-character bound has NO sqrt(q) saving;",flush=True)
print("the elementary-symmetric e_a does not inherit per-element cancellation on thin mu_n.",flush=True)
