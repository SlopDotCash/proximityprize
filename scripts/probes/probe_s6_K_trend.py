#!/usr/bin/env python3
"""
S6 K-TREND probe (#444): separate the STRONG S6 claim (spur=0, Deligne main-term) from the WEAK
claim the prize needs (E_r <= K^r * Wick, K=O(1)).

At FIXED prize beta=4 (p = smallest prime =1 mod n above n^4):
  K_Fp(n,r) = (E_r^{Fp} / Wick)^{1/r}.
Questions:
 (1) Is K_Fp bounded & antitone in r (at fixed n)?  -> weak claim alive (= BGK wall, not Deligne).
 (2) Is K_Fp flat in n (at fixed r)?  -> n-independence of the WEAK constant.
 (3) spur=0?  -> strong Deligne claim. (We already know: only r<=3.)
We push r as far as conv allows at n=8,16 (p<= 8^4=4096, 16^4=65537 -> conv cheap, high r ok).
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

def doubleFactOdd(r):
    d=1
    for k in range(1,2*r,2): d*=k
    return d

def wick(n,r): return doubleFactOdd(r)*n**r

def prime_above(n,target):
    p=target+((1-target)%n)
    if p<target: p+=n
    if p<2: p=1+n
    while not is_prime(p): p+=n
    return p

print("S6 K-TREND at PRIZE beta=4 (p = smallest prime =1 mod n above n^4).")
print("K_Fp=(E_Fp/Wick)^{1/r}; K_c0=(E_c0/Wick)^{1/r}; spur/E_c0 = char-p excess.")
for n in (8,16):
    p=prime_above(n, n**4); S=mu_n(p,n); beta=math.log(p)/math.log(n)
    print(f"\n=== n={n}, p={p}, beta={beta:.3f} ===")
    print(f"{'r':>2} | {'E_Fp':>20} | {'spur/E_c0':>12} | {'K_Fp':>7} | {'K_c0':>7} | strong(spur=0)?")
    rmax = 14 if n==8 else 11
    for r in range(2, rmax):
        c0=char0(n,r); Ep=energy_conv(p,S,r); spur=Ep-c0; w=wick(n,r)
        kfp=(Ep/w)**(1/r); kc0=(c0/w)**(1/r); rel=spur/c0 if c0 else 0
        strong = "YES (spur=0)" if spur==0 else "no"
        print(f"{r:>2} | {Ep:>20d} | {rel:12.6f} | {kfp:7.4f} | {kc0:7.4f} | {strong}")

print("\nn-FLATNESS of K_Fp at fixed r, beta=4 (is the weak constant n-independent?):")
print(f"{'r':>2} | " + " | ".join(f"n={n}".rjust(9) for n in (8,16,32)))
for r in range(2,7):
    cells=[]
    for n in (8,16,32):
        p=prime_above(n,n**4)
        if p>6*10**7: cells.append("  (skip)"); continue
        S=mu_n(p,n); Ep=energy_conv(p,S,r); w=wick(n,r)
        cells.append(f"{(Ep/w)**(1/r):9.4f}")
    print(f"{r:>2} | " + " | ".join(cells))

print("\nINTERPRET:")
print(" STRONG claim (spur=0 / Deligne main-term K=1 or K=4): TRUE only r<=3 at beta=4 -> REFUTED deep.")
print(" WEAK claim (K_Fp=O(1) bounded & antitone, n-flat): if it holds, that IS the BGK/Paley wall,")
print(" NOT something Deligne proves -- Deligne's spur bound grows past r_max=2beta-3=5.")
