#!/usr/bin/env python3
"""
Cycle-2 probe: is the TOP-BLOCK-ZERO structure (delta_k=0 on the top T levels at worst-b)
n-stable, and how large is T? This decides whether a "top block forces a 2^T factor in the
dilation budget" lemma is a real, non-vacuous constraint.

If at worst-b the first T levels have delta_k=0 (same-ray, factor exactly 2 each), then
M_T = 2^T * M_0 along that block (no saving), and ALL the route's saving must come from the
bottom a-T levels. We measure T (the count of leading zero-deficit levels) across n,
multiple structured primes, to see if T grows (=> top block is a hard 2^T wall) or is small/noisy.
"""
import cmath, math

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, beta=3.2):
    target = int(n**beta)
    p = target - (target % n) + 1
    if p < target: p += n
    while not is_prime(p):
        p += n
    return p

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
        if all(pow(g,phi//q,p)!=1 for q in factors): return g

def subgroup(p,n,g):
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def eta(b,S,p):
    return sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)

def worst_b(S,p):
    seen=bytearray(p); best=-1.0; bb=None
    for b in range(1,p):
        if seen[b]: continue
        for c in S: seen[(b*c)%p]=1
        v=abs(eta(b,S,p))
        if v>best: best,bb=v,b
    return bb,best

def leading_zero_levels(p,a,b,g,tol=1e-9):
    T=0
    for k in range(a):
        order=2**(a-k)
        if order<2: break
        h=pow(g,(p-1)//order,p); elems=[]; x=1
        for _ in range(order): elems.append(x); x=(x*h)%p
        half=order//2
        P0=sum(cmath.exp(2j*math.pi*(b*elems[2*i]%p)/p) for i in range(half))
        P1=sum(cmath.exp(2j*math.pi*(b*elems[2*i+1]%p)/p) for i in range(half))
        denom=abs(P0)+abs(P1)
        rho=abs(P0+P1)/denom if denom>1e-12 else 1.0
        delta=1.0-rho
        if delta<=tol:
            T+=1
        else:
            break
    return T

print(f"{'a':>2} {'n':>4} {'beta':>5} {'p':>10} {'T(lead-zero)':>12} {'a-T':>4}")
for beta in [3.2, 4.0]:
    for a in range(3,7):
        n=2**a; p=find_prime(n,beta); g=primitive_root(p)
        S=subgroup(p,n,g); b,_=worst_b(S,p)
        T=leading_zero_levels(p,a,b,g)
        print(f"{a:>2} {n:>4} {beta:>5} {p:>10} {T:>12} {a-T:>4}")
