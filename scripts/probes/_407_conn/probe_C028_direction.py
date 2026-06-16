# -*- coding: utf-8 -*-
import functools, itertools, math
print = functools.partial(print, flush=True)
from sympy import isprime
"""
C028 sub-claim (4), sharpened — the DIRECTION / complement claim.

C028 says: "list explosion needs sums DISTINCT (R(g)!=0), floor cleanliness needs
bad relations to VANISH (R(g)=0). Exact complements gated by p <=> s^{s/2}."
And: "p > s^{s/2} gives the ceiling, p <= s^{s/2} would give the floor."

We REFUTE the complement structure by direct measurement of BOTH faces in the SAME
prize field F_q (q ~ n^4, mu_n PROPER subgroup):

  FACE-A (F4 distinctness):  among collision polys R=P-Q (deg<n/2, ||R||_1<=2r),
     count how many actually VANISH at g mod q  (#collisions).
     - p>s^{s/2}  =>  ZERO vanish  (KKH26 distinctness, proven).
     - prize p<<s^{s/2} => some MAY vanish (char-p surplus); count them.

  FACE-B (F10 floor):  #lacBad <= C*n ?   measured in the SAME field.

C028 predicts these are COMPLEMENTARY: when p<=s^{s/2} (prize), F4 distinctness
fails (collisions appear) AND, by the "flip", F10 vanishing/floor should hold cleanly.
We test whether (i) the prize prime actually produces F4 collisions, and (ii) whether
the F10 floor holds or fails, INDEPENDENTLY -- to see if they are really one knob.
"""

def find_prime(n, beta=4):
    lo=int(n**beta); q=lo-(lo%n)+1
    if q<lo: q+=n
    while not isprime(q): q+=n
    return q

def pfac(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f

def prim_root(q,n):
    e=(q-1)//n
    for b in range(2,q):
        g=pow(b,e,q)
        if g==1: continue
        if all(pow(g,n//p,q)!=1 for p in pfac(n)): return g
    raise RuntimeError

def esymm(vals,t,q):
    e=[0]*(t+1); e[0]=1
    for v in vals:
        for k in range(min(t,t),0,-1):
            e[k]=(e[k]+v*e[k-1])%q
    return e[t]%q

def eval_poly(R, g, q):
    return sum(c*pow(g,e,q) for e,c in R.items())%q

def collision_polys(half, r):
    sigs=[]
    for U in itertools.combinations(range(half), r):
        for signs in itertools.product([1,-1],repeat=r):
            p={}
            for e,s in zip(U,signs): p[e]=p.get(e,0)+s
            sigs.append({k:v for k,v in p.items() if v})
    seen=set(); out=[]
    for i in range(len(sigs)):
        for j in range(len(sigs)):
            if i==j: continue
            R={}
            for e in set(sigs[i])|set(sigs[j]):
                c=sigs[i].get(e,0)-sigs[j].get(e,0)
                if c: R[e]=c
            if not R: continue
            k=tuple(sorted(R.items()))
            if k in seen: continue
            seen.add(k); out.append(R)
    return out

def main():
    print("=== FACE-A (F4): char-p collisions at PRIZE prime (p << s^{s/2}) ===")
    print("Count collision polys R=P-Q (deg<n/2,||R||_1<=2r) that VANISH at g mod q.")
    print(f"{'n':>4} {'q(~n^4)':>10} {'r':>2} {'#R':>6} {'#vanish@g':>10} {'log2(s^(s/2)/p)':>16}")
    for mu in [3,4,5]:
        n=2**mu; half=n//2; q=find_prime(n,4); g=prim_root(q,n)
        rlist=[2,3] if mu<=4 else [2]
        for r in rlist:
            if r>half: continue
            Rs=collision_polys(half,r)
            vanish=sum(1 for R in Rs if eval_poly(R,g,q)==0)
            log2_thr = mu*(2**(mu-1)); log2_p = math.log2(q)
            print(f"{n:>4} {q:>10} {r:>2} {len(Rs):>6} {vanish:>10} {log2_thr-log2_p:>16.1f}")
    print()
    print("=== Are the two faces ONE knob? F4-collision-free  vs  F10-floor-holds ===")
    print("If C028's complement holds, prize (p<<thr) should show F4 COLLISIONS while")
    print("F10 floor stays CLEAN -> one knob flipped. Measure both in same field.")
    print(f"{'n':>4} {'q':>10} {'F4 #vanish(r=2)':>16} {'F10 #lacBad(a=4,t=2)':>22} {'floor<=4n':>10}")
    for mu in [3,4]:
        n=2**mu; half=n//2; q=find_prime(n,4); g=prim_root(q,n)
        Rs=collision_polys(half,2)
        f4=sum(1 for R in Rs if eval_poly(R,g,q)==0)
        # F10
        mu_set=[pow(g,i,q) for i in range(n)]
        a,t=4,2
        lac=set()
        for S in itertools.combinations(mu_set,a):
            if all(esymm(S,j,q)==0 for j in range(1,t)):
                lac.add(esymm(S,t,q))
        print(f"{n:>4} {q:>10} {f4:>16} {len(lac):>22} {str(len(lac)<=4*n):>10}")

if __name__=="__main__":
    main()
