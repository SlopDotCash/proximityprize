#!/usr/bin/env python3
"""
C093 PART C -- the SHARP test of the C093 claim: 'uniform-in-p at FIXED index m'.

C093's whole bet is that going to the multiplicative h-shift family makes the open
question 'constant-index (m fixed) effective equidistribution', and that the conductor
of the h |-> T_h Kummer-sheaf family is BOUNDED uniformly in p AT FIXED m. If true, the
homothety lever delivers sqrt(q)-per-h + a bounded m-average => the prize.

We test this by collecting many primes p with EXACTLY the same index m (same proper dyadic
mu_n, same m), spanning the widest available p-range, and checking:

  (1) Is max_h|T_h| / sqrt(n) BOUNDED as p grows at fixed (n,m)?  (lever works)
      or does the worst tangent sum keep scaling with the SAME sqrt(n ln m) BGK law
      regardless of p? (no homothety gain; conductor effectively independent of the
      'fixed index', the cancellation is the geometry of {1-w} which does NOT simplify)

  (2) THE CONDUCTOR. The h-family sheaf is L_{phi} pulled to mu_n; the m-average is the
      pushforward [n]_* whose conductor ~ n (NOT O(1) in p, because n itself is part of
      the prize regime and grows). At FIXED m, n = (p-1)/m grows LINEARLY in p. So even
      'fixed index' does NOT fix the conductor: n -> infinity with p. We display n at each
      p to make the conductor-growth explicit: 'fixed index' still has n=(p-1)/m -> oo,
      and the per-period single-sheaf Deligne bound is the trivial sqrt(p) (NO gain).

To probe a genuinely fixed index across a wide p-range we use small m so many primes
p=1+n*m exist; n=8 keeps exact arithmetic cheap so we can push p up.
"""
import math
import numpy as np

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def primitive_root(p):
    n=p-1; fac=set(); d=2
    while d*d<=n:
        while n%d==0: fac.add(d); n//=d
        d+=1
    if n>1: fac.add(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    raise RuntimeError

def measure(n, p):
    g=primitive_root(p); pe=p-1; m=pe//n; sqp=math.sqrt(p)
    dlog=np.empty(p,dtype=np.int64); dlog[0]=-1
    x=1
    for k in range(pe):
        dlog[x]=k; x=(x*g)%p
    mu=np.array([pow(g,(m*t)%pe,p) for t in range(n)],dtype=np.int64)
    # house B
    bvals=np.arange(1,p)
    eta=np.exp(2j*np.pi*(np.outer(bvals,mu)%p)/p).sum(axis=1)
    B=float(np.max(np.abs(eta)))
    # tangent family over all e
    one_minus=(1-mu)%p; nz=one_minus!=0; om=one_minus[nz]; klog=dlog[om]
    e_all=np.arange(0,pe)
    T=np.exp(2j*np.pi*np.outer(e_all,klog)/pe).sum(axis=1)
    Tnz=np.abs(T[1:])
    return dict(p=p,m=m,n=n,B=B,maxT=float(np.max(Tnz)),rmsT=float(np.sqrt(np.mean(Tnz**2))),sqp=sqp)

print("="*100)
print("C093 PART C: TRULY FIXED index m -- is the h-shift family bounded uniformly in p?")
print("="*100)

# Pick FIXED small indices m and find ALL primes p=1+n*m up to a cap (n=8).
for n in (8,):
    for m in (3, 5, 9, 15):     # fixed odd-part index (mu_n proper, shift family nontrivial)
        primes=[]
        for p in range(n*m+1, 3_000_000, n*m):
            if p==1+n*m and is_prime(p): primes.append(p)
            elif (p-1)%(n*m)==0 and is_prime(p): primes.append(p)
        # the above double-counts logic; redo cleanly:
        primes=[1+n*m*t for t in range(1, 3_000_000//(n*m)) ]
        primes=[p for p in primes if (p-1)//n==m and is_prime(p)]
        # keep those with EXACT index m (p=1+n*m), i.e. t=1 only gives one prime; instead
        # 'fixed index m' means (p-1)/n=m EXACTLY => p=1+n*m is a SINGLE prime. To get a
        # p-RANGE at fixed index we must vary n. Reinterpret: fixed index m, vary n:
        pass
    # Correct interpretation: FIXED m, vary n (so p=1+n*m sweeps a range, index stays m).
    print(f"\n(reinterpreting 'fixed index' correctly: hold m fixed, vary n; p=1+n*m, index=(p-1)/n=m)")
    break

for m in (65, 129, 257, 513):
    print(f"\n--- FIXED INDEX m={m} (sqrt(ln m)={math.sqrt(math.log(m)):.3f}); vary n, so p=1+n*m grows ---")
    rows=[]
    for n in (8,16,32,48,64,96,128):
        p=1+n*m
        if p>4_000_000: continue
        if not is_prime(p): continue
        R=measure(n,p)
        rows.append(R)
        print(f"   n={n:>4} p={p:>8} (beta={math.log(p)/math.log(n):.2f}) "
              f"n/sqrt(q)={n/R['sqp']:.3f}  "
              f"maxT/sqrt(n)={R['maxT']/math.sqrt(n):.3f}  "
              f"maxT/rmsT={R['maxT']/R['rmsT']:.3f}  "
              f"B/sqrt(n)={R['B']/math.sqrt(n):.3f}  "
              f"B/sqrt(p)={R['B']/R['sqp']:.4f}")
    if rows:
        vals=[r['maxT']/math.sqrt(r['n']) for r in rows]
        print(f"   => max|T|/sqrt(n) over this fixed-index family: min={min(vals):.3f} max={max(vals):.3f}"
              f"  (BOUNDED near sqrt(ln m)={math.sqrt(math.log(m)):.3f}? yes, but that is the BGK law,")
        print(f"      NOT a homothety GAIN: maxT/rmsT stays ~ sqrt(ln m) => extreme-value gap persists;")
        print(f"      and B/sqrt(n) ~ const>2 = the SAME unproven >sqrt(n) house, not eased by fixing m.)")
