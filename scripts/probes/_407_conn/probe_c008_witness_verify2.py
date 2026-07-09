#!/usr/bin/env python3
"""C008 verification (fixed): the resultant vanishing q|Res means e2Fold has SOME
primitive 2^m-th root g mod q as a root, not an arbitrary one. Enumerate ALL primitive
2^m-th roots g in F_q and check e2(A,g)=0 for at least one. Evaluate via e2Fold directly
(matches Lean) to avoid exponent-reduction confusion."""
from sympy import factorint, isprime, primitive_root
import math

def e2fold_coeffs(m, A):
    n=2**m; h=2**(m-1); coeff=[0]*h; Al=sorted(A)
    for a in range(len(Al)):
        for b in range(a+1,len(Al)):
            e=(Al[a]+Al[b])%n
            if e<h: coeff[e]+=1
            else: coeff[e-h]-=1
    return coeff  # index t -> coeff of X^t, t in [0, h)

def eval_fold(coeff, g, q):
    s=0; gp=1
    for c in coeff:
        if c: s=(s + c*gp)%q
        gp=(gp*g)%q
    return s%q

def all_primitive_2m_roots(q, m):
    """all g with order exactly 2^m in F_q*."""
    n=2**m
    pr=primitive_root(q)
    base=pow(pr,(q-1)//n,q)   # one primitive 2^m-th root
    roots=[]
    for e in range(1,n):
        if math.gcd(e,n)==1:
            roots.append(pow(base,e,q))
    return roots

m=5; n=2**m
A={1,5,6,7,8,10,19,20,23,27,28,31}
coeff=e2fold_coeffs(m,A)
q=139292647009
assert isprime(q) and q%n==1
roots=all_primitive_2m_roots(q,m)
vals=[eval_fold(coeff,g,q) for g in roots]
zeros=[g for g,v in zip(roots,vals) if v==0]
print(f"n={n} q={q} (beta=log_n q={math.log(q,n):.2f}, proper subgroup index={(q-1)//n})")
print(f"#primitive 2^{m}-th roots = {len(roots)}; #roots with e2Fold(g)=0 mod q = {len(zeros)}")
print(f"zero-roots g = {zeros}")
print(f"==> BAD ALPHA (genuine e2 collision at proper-subgroup prize prime) EXISTS: {len(zeros)>0}")

# Cross-check: e2(A,g) via raw power-sum at a zero root equals 0 too.
if zeros:
    g=zeros[0]
    Al=sorted(A); raw=0
    for a in range(len(Al)):
        for b in range(a+1,len(Al)):
            raw=(raw+pow(g,(Al[a]+Al[b])%n,q))%q
    print(f"raw e2(A,g)=sum g^(i+j) mod q at zero-root g={g}: {raw}  (should be 0)")
