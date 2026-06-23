#!/usr/bin/env python3
"""
SINGLE FRONTIER QUESTION (door-iv Lane-3, genuinely unmapped at a>=7):
does the bottom-block deficit count (a-T) GROW with a, or stay O(1)?
T = leading zero-deficit (rho=1, same-ray) levels at worst-b along the 2-dilation descent.
Prior probe stopped at a=6 (a-T = 1,1,1,3). If a-T grows ~linearly the dilation route has a
live crack; if it stays O(1) the leading-zero-block wall is confirmed asymptotically.
Proper thin mu_n subset F_p*, p~n^3.2, FULL F_p* coset-deduped worst-b argmax, NEVER n=q-1.
"""
import math
def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True
def find_prime(n,beta=3.2):
    t=int(n**beta); p=t-(t%n)+1
    if p<t: p+=n
    while not is_prime(p): p+=n
    return p
def primitive_root(p):
    phi=p-1; m=phi; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
def subgroup(p,n,g):
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=x*h%p
    return S
def eta_abs2(b,S,p):
    cr=ci=0.0
    for x in S:
        t=2*math.pi*((b*x)%p)/p
        cr+=math.cos(t); ci+=math.sin(t)
    return cr*cr+ci*ci
def worst_b(S,p):
    seen=bytearray(p); best=-1.0; bb=1
    for b in range(1,p):
        if seen[b]: continue
        for c in S: seen[(b*c)%p]=1
        v=eta_abs2(b,S,p)
        if v>best: best,bb=v,b
    return bb
def leading_zero_levels(p,a,b,g,tol=1e-9):
    T=0
    for k in range(a):
        order=2**(a-k)
        if order<2: break
        h=pow(g,(p-1)//order,p); elems=[]; x=1
        for _ in range(order): elems.append(x); x=x*h%p
        half=order//2
        c0r=c0i=c1r=c1i=0.0
        for i in range(half):
            t0=2*math.pi*((b*elems[2*i])%p)/p
            t1=2*math.pi*((b*elems[2*i+1])%p)/p
            c0r+=math.cos(t0); c0i+=math.sin(t0)
            c1r+=math.cos(t1); c1i+=math.sin(t1)
        P0=math.hypot(c0r,c0i); P1=math.hypot(c1r,c1i)
        denom=P0+P1
        rho=math.hypot(c0r+c1r,c0i+c1i)/denom if denom>1e-12 else 1.0
        if (1.0-rho)<=tol: T+=1
        else: break
    return T
print(f"{'a':>2} {'n':>4} {'beta':>4} {'p':>11} {'b*':>10} {'T':>3} {'a-T':>4}")
for beta in [3.2]:
    for a in [5,6,7]:
        n=2**a; p=find_prime(n,beta); g=primitive_root(p)
        S=subgroup(p,n,g); b=worst_b(S,p)
        T=leading_zero_levels(p,a,b,g)
        print(f"{a:>2} {n:>4} {beta:>4} {p:>11} {b:>10} {T:>3} {a-T:>4}",flush=True)
