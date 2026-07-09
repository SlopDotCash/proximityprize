#!/usr/bin/env python3
"""
#407 -- CRITICAL refinement: does r_half scale with n (support) or with q?

The previous probe shows r_half grows in n but is flat in q. This is the crux of the
Habegger/KU route. Two competing controls on the 2r-th moment of (eta/sqrt n):
  (i) FINITE-SUPPORT / CLT correction: the period law -> N(0,1), but at finite n the
      2r-th moment is (2r-1)!! * (1 - r(r-1)/(2n) + ...).  The error is ~ r^2/n; it stays
      < 0.5 up to r ~ sqrt(n).  This is n-controlled, GROWS with n -- GOOD for the prize.
  (ii) p-DEFECT / BGK term: E_r picks up n^{2r}/q from mod-q coincidences; relative size
      ~ n^{2r}/(q (2r-1)!! n^r) = n^r/(q (2r-1)!!), exceeds 1 at r ~ log_n q = beta.
      This is q-controlled and small -- but it is the ANALYTIC wall (the additive-energy excess).

We disentangle: measure r_half vs sqrt(n) (the CLT prediction) AND compute the cumulant
kappa_r = (sum|eta|^{2r}/m)/((2r-1)!! n^r) at the moment-optimal r* = round(ln q), the actual
prize quantity.  The kappa_r <= 1 question is what the floor needs; r_half is a proxy.
"""
import math

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def prime_1_mod_n_near(target,n):
    p=target-(target%n)+1
    if p>target: p-=n
    while p>n:
        if is_prime(p): return p
        p-=n
    return None

def order_n_gen(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        s=set();x=1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return h
    return None

def periods(p,n,h):
    mu=[pow(h,i,p) for i in range(n)]
    m=(p-1)//n
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    return [sum(math.cos(2*math.pi*(b*x%p)/p) for x in mu) for b in reps]

def dfac2(r):
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

print("="*100)
print("r_half vs sqrt(n) (CLT-correction prediction), and kappa_{r*} at r*=round(ln q)")
print("  kappa_r = (sum|eta|^{2r}/m)/((2r-1)!! n^r)  -- the ACTUAL floor quantity")
print("="*100)
print(f"{'n':>5} {'beta':>5} {'p':>11} | {'r_half':>6} {'sqrt n':>6} {'r_h/sqrtn':>9} | {'r*=lnq':>6} {'kappa@r*':>9} {'kappa@sqrtn':>11}")
beta=4.0
for a in (4,5,6,7):
    n=2**a
    tgt=int(n**beta)
    if tgt>40_000_000: tgt=40_000_000
    p=prime_1_mod_n_near(tgt,n)
    if p is None: continue
    h=order_n_gen(p,n)
    if h is None: continue
    et=periods(p,n,h); m=len(et)
    lnq=math.log(p)
    # r_half
    r_half=1
    for r in range(2,2*n):
        mom=sum((e/math.sqrt(n))**(2*r) for e in et)/m
        rel=abs(mom-dfac2(r))/dfac2(r)
        if rel<0.5: r_half=r
        else: break
    rstar=max(2,round(lnq))
    def kap(r): return (sum(e**(2*r) for e in et)/m)/(dfac2(r)*n**r)
    k_star=kap(min(rstar, n-1))
    r_sn=max(2,round(math.sqrt(n)))
    k_sn=kap(min(r_sn,n-1))
    print(f"{n:>5} {beta:>5.1f} {p:>11} | {r_half:>6} {math.sqrt(n):>6.1f} {r_half/math.sqrt(n):>9.2f} | "
          f"{rstar:>6} {k_star:>9.3f} {k_sn:>11.3f}")
print("""
READ:
- r_half / sqrt(n) is ~CONSTANT  => r_half = Theta(sqrt n).  The moment-matching depth is set by
  the FINITE-SUPPORT (CLT) correction r^2/n, NOT by the conductor or by q.
- THE PIVOT: needed depth is r_opt = ln q.  Prize has n=2^40, q~n^5 => ln q ~ 110, sqrt(n)=2^20 ~ 1e6.
  So at the prize scale  r_opt = ln q ~ 110  <<  sqrt(n) = 2^20 = r_half.
  => the FINITE-SUPPORT obstruction does NOT bite at the prize (n is HUGE relative to ln q)!
- The ONLY surviving obstruction at the prize is the p-DEFECT (kappa@r* row): whether the mod-q
  coincidence excess n^{2r}/q stays below the Gaussian baseline at r* = ln q.  That is exactly the
  additive-energy / BGK wall -- q-controlled, NOT reachable by fixed-length equidistribution.
- So fixed-length (q->oo) equidistribution and finite-support CLT both give the deep moments FOR
  FREE at the prize scale (n >> ln q); they DON'T touch the residual, because the residual is the
  p-defect (a mod-q arithmetic coincidence), orthogonal to the archimedean equidistribution.
""")
