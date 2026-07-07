"""
probe_444_boundA_r3reverse.py -- reverse-engineer the EXACT r=3 invariant J -> C(n/4,2) bijection.

We know: bad S={a,b sq}U{c,d nsq}, ab=-cd, all in mu_n. J=gamma^{n/d}, d=1 (e-f=1), so J=gamma^n.
gamma=-h_{n/2-3}(S)/h_{n/2-4}(S).
O_P = C(n/4,2). So J <-> a 2-subset of a set of size n/4.

We compute J for each bad S and try to MATCH it to a 2-subset of mu_{n/4}=<w^4> (fourth powers),
or to {i,j} pairs derived from indices via i+j or i-j reduced mod n/4, etc.

Candidate maps from S=(a=w^A, b=w^B even; c=w^C, d=w^D odd, A+B = C+D + n/2 mod n since ab=-cd
 and -1=w^{n/2}):
   m1: {A,B} mod (n/2)  -> reduces to squares index pair; but #distinct = C(n/2,2)? too big.
   m2: {A-B mod n}  (difference) -> the diff-set; M2 said const per J only at r=3. test size.
   m3: the pair {(A+B)/2-ish} ... we just BRUTE-FORCE which simple index functional is constant
       per J AND takes exactly C(n/4,2) distinct values.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES=[2013265921,3221225473]
def gen(n,p):
    e=(p-1)//n
    for c in range(2,2000):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def collect(n,p):
    r=3; e,f=n//2,n//2-1; a0=4; w=gen(n,p); d=gcd((e-f)%n,n); nd=n//d
    M=max(e-r+1,f-r+1)
    rows=[]
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,M,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J=pow(g,nd,p)
        sq=sorted(i for i in Sidx if i%2==0); nsq=sorted(i for i in Sidx if i%2==1)
        rows.append((J,tuple(sq),tuple(nsq),tuple(sorted(Sidx))))
    return rows,n

def test_functional(rows,name,fn,n):
    """fn(sq,nsq) -> hashable. Check const per J and #distinct."""
    J2v=defaultdict(set); v2J=defaultdict(set)
    for J,sq,nsq,S in rows:
        v=fn(sq,nsq,S,n); J2v[J].add(v); v2J[v].add(J)
    const=all(len(s)==1 for s in J2v.values())
    inj=all(len(s)==1 for s in v2J.values())
    ndist=len(v2J); OP=len(J2v)
    bij = const and inj and ndist==OP
    print(f"     [{name}] const-per-J={const} inj={inj} #vals={ndist} O_P={OP} BIJECTION={bij}")
    return bij

if __name__=="__main__":
    for p in PRIMES[:1]:
        print(f"### p={p}")
        for n in [16,32]:
            rows,_=collect(n,p)
            print(f"  n={n}: O_P={len(set(r[0] for r in rows))} C(n/4,2)={comb(n//4,2)}")
            half=n//2; quart=n//4
            # functionals to test:
            # squares indices A,B even -> /2 gives squares as elements of Z_{n/2}; further the
            # antipodal pair within squares: A and A+n/2 are antipodal. fold to Z_{n/2} then the
            # 'unordered pair mod n/4'? try several.
            test_functional(rows,"sq-pair {A,B}",            lambda sq,ns,S,n: tuple(sorted(sq)),n)
            test_functional(rows,"sq-pair/2 {A/2,B/2}",      lambda sq,ns,S,n: tuple(sorted(i//2 for i in sq)),n)
            test_functional(rows,"sq A+B mod n",             lambda sq,ns,S,n: sum(sq)%n,n)
            test_functional(rows,"sq A-B mod n",             lambda sq,ns,S,n: (sq[1]-sq[0])%n,n)
            test_functional(rows,"{A-B mod n/2 fold}",       lambda sq,ns,S,n: min((sq[1]-sq[0])%(n//2),(sq[0]-sq[1])%(n//2)),n)
            # unordered antipodal-fold of square indices to Z_{n/4}: i -> i mod n/2 then mod n/4
            test_functional(rows,"sq {A,B} mod n/4 unord",   lambda sq,ns,S,n: tuple(sorted({(i//2)%(n//4) for i in sq})),n)
            test_functional(rows,"sqset+nsqset diff",        lambda sq,ns,S,n: (frozenset(sq),frozenset(ns)),n)
            # the pair {A//2 , B//2} as a 2-subset of Z_{n/2} (squares=mu_{n/2}); is it C(n/2,2)?
            # but we want C(n/4,2). try (A//2 mod n/4, B//2 mod n/4) unordered as 2-subset of Z_{n/4}
            test_functional(rows,"sq idx//2 mod n/4 set",    lambda sq,ns,S,n: frozenset((i//2)%(n//4) for i in sq),n)
            # difference of square element indices halved
            test_functional(rows,"(A-B)//2 fold n/4",        lambda sq,ns,S,n: min(((sq[1]-sq[0])//2)%(n//4),((sq[0]-sq[1])//2)%(n//4)) if (sq[1]-sq[0])%2==0 else -1,n)
