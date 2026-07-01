#!/usr/bin/env python3
"""
S6 BETA-BAND probe (#444), FAST & DECISIVE.

For each (n,r): test spur_r(p) at the SMALLEST prime p=1 mod n with beta = log_n(p) just above each
target in {3.0, 3.5, 4.0, 4.5, 5.0, 5.5}. Report spur and spur/E_c0. The threshold beta*(n,r) is the
smallest target band where spur becomes 0 (and stays 0). Only ONE energy eval per (n,beta) => fast.

This directly answers: at the GENUINE PRIZE beta=4, for which r is the transfer (spur=0) valid?
 - If valid only for r <= ~3 (and the threshold beta* climbs with r ~ (r+3)/2): REDUCES TO WALL.
 - If valid for all r at beta=4: genuine route.

Char-0 exact (cyclotomic). Char-p exact via convolution mod p (we keep p moderate by choosing the
SMALLEST prime above each n^beta, so p <= n^5.5; for n<=32 that's <= ~3.3e7 but we cap n=32 at b<=4.5).
"""
import math
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d,s=m-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def primitive_root(p):
    phi=p-1; m=phi; fac=[]; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=x*h%p
    assert len(S)==n
    return sorted(S)

def energy_conv(p,S,r):
    dist=defaultdict(int); dist[0]=1
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for x in S: nd[(s+x)%p]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def root_vec(n,k):
    half=n//2; k%=n; v=[0]*half
    if k<half: v[k]=1
    else: v[k-half]=-1
    return tuple(v)

def char0(n,r):
    half=n//2; dist=defaultdict(int); dist[tuple([0]*half)]=1
    rv=[root_vec(n,k) for k in range(n)]
    for _ in range(r):
        nd=defaultdict(int)
        for vec,c in dist.items():
            for w in rv:
                nv=tuple(vec[t]+w[t] for t in range(half)); nd[nv]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def prime_above(n, target):
    p = target + ((1-target)%n)
    if p<target: p+=n
    if p<2: p=1+n
    while not is_prime(p): p+=n
    return p

bands = [3.0, 3.5, 4.0, 4.5, 5.0, 5.5]
print("="*108)
print("S6 BETA-BAND: spur_r(p)/E_c0 at smallest prime p just above n^beta, for each beta band.")
print("  spur=0 == char-p energy EXACTLY equals char-0 == transfer VALID at that (n,r,beta).")
print("  PRIZE column is beta=4.0.  Threshold beta*(n,r) = first band where spur hits 0.")
print("="*108)

for n in (8, 16, 32):
    print(f"\n=== n={n} ===")
    print(f"{'r':>2} | " + " | ".join(f"b={b}".rjust(11) for b in bands) + " | beta*(spur->0)")
    for r in range(2, 9):
        c0 = char0(n, r)
        cells=[]; bstar=None
        for b in bands:
            target = int(round(n**b))
            p = prime_above(n, target)
            if p > 6*10**7:   # too big for conv; mark skip
                cells.append("   (skip)"); continue
            S = mu_n(p, n)
            Ep = energy_conv(p, S, r)
            spur = Ep - c0
            rel = spur/c0 if c0 else float('nan')
            cells.append(f"{rel:11.6f}")
            if spur==0 and bstar is None:
                bstar=b
        bs = f"{bstar}" if bstar is not None else ">5.5"
        print(f"{r:>2} | " + " | ".join(cells) + f" | {bs}   [(r+3)/2={(r+3)/2:.1f}]")

print("\n"+"="*108)
print("READ: PRIZE is the b=4.0 column. A nonzero entry there == transfer FAILS at that depth r at")
print("the genuine prize field size. If beta*(spur->0) climbs with r tracking (r+3)/2, the spur=0")
print("onset (== Deligne error < budget) needs p ~ n^{(r+3)/2}: the controlling defect GROWS with n.")
print("="*108)
