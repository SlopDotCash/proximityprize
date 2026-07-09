#!/usr/bin/env python3
"""
probe_house_vs_fourthmoment_407.py  (#407 — the potential-CLOSURE test)

The house B = max_{b!=0}|sum_{x in mu_n} e_p(bx)| has power spectrum whose L^2 (4th moment) is
N = #{(w,w') in mu_n^2 : (1-w)/(1-w') in mu_n} = E_2-equivalent, which is PROVEN computable
(N ~ 2n-3 forced + extra bad-prime coincidences, all <= O(n) since n^4 < p).

BOLD CONJECTURE TO TEST: the house CONSTANT C = B/sqrt(n ln m) is a CLOSED FUNCTION of (N/n, m) --
i.e. the deep moments (which govern the L^inf house) COLLAPSE onto the 4th moment N. If TRUE: since
N is exactly computable, delta* is CLOSED (no open analytic input). If FALSE (C has large residual
scatter at fixed N/n): the house needs deep structure beyond N => wall confirmed, decisively.

Method: scan many primes per n; for each compute B (FFT), m, N (fibers of s->s^n on {1-w}), C, N/n.
Tabulate C grouped by N/n bucket: if C is tight within a bucket => closed; if wide => open.
"""
import numpy as np, math
from collections import defaultdict

def is_prime(x):
    if x<2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x%w==0: return x==w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(a,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True

def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        s,x=set(),1
        for _ in range(n):
            s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    return None

def house_and_N(p,n):
    mu=subgroup(p,n)
    if mu is None: return None
    m=(p-1)//n
    f=np.zeros(p)
    for x in mu: f[x]=1.0
    S=np.fft.fft(f); a=np.abs(S); a[0]=0.0
    B=float(np.max(a))
    # N via fibers of s->s^n on T={1-w, w!=1}
    fib=defaultdict(int)
    for w in mu:
        if w!=1:
            fib[pow((1-w)%p,n,p)]+=1
    N=sum(c*c for c in fib.values())
    C=B/math.sqrt(n*math.log(m)) if m>1 else float('nan')
    return B,m,N,C,N/n

if __name__=="__main__":
    print("# Is house constant C = B/sqrt(n ln m) a closed function of 4th-moment N/n? (#407)\n")
    for n in [16,32,64]:
        rows=[]
        k=2
        while len(rows)<60:
            p=k*n+1; k+=1
            if p>400000: break
            if (p-1)%n==0 and is_prime(p) and p>n*n:
                r=house_and_N(p,n)
                if r: rows.append((p,)+r)
        if not rows: continue
        # bucket by N/n rounded to 0.25, report C mean/std/spread per bucket
        buckets=defaultdict(list)
        for (p,B,m,N,C,Nn) in rows:
            buckets[round(Nn*4)/4].append(C)
        print(f"n={n}: {len(rows)} primes.  C grouped by N/n bucket (tight C => closure; wide => wall):")
        print(f"   {'N/n':>6} {'#':>4} {'meanC':>7} {'stdC':>6} {'minC':>6} {'maxC':>6} {'spread':>7}")
        for nn in sorted(buckets):
            cs=buckets[nn]
            if len(cs)>=2:
                mean=sum(cs)/len(cs); std=(sum((c-mean)**2 for c in cs)/len(cs))**0.5
                print(f"   {nn:>6.2f} {len(cs):>4} {mean:>7.3f} {std:>6.3f} {min(cs):>6.3f} {max(cs):>6.3f} {max(cs)-min(cs):>7.3f}")
        allC=[r[4] for r in rows]; aN=[r[5] for r in rows]
        # correlation of C with N/n
        mc=sum(allC)/len(allC); mn=sum(aN)/len(aN)
        cov=sum((c-mc)*(x-mn) for c,x in zip(allC,aN))/len(allC)
        sc=(sum((c-mc)**2 for c in allC)/len(allC))**0.5
        sn=(sum((x-mn)**2 for x in aN)/len(aN))**0.5
        corr=cov/(sc*sn) if sc*sn>0 else 0
        print(f"   => overall corr(C, N/n) = {corr:.3f};  C range [{min(allC):.3f},{max(allC):.3f}] std {sc:.3f}\n")
    print("VERDICT: if within-bucket spread << between-bucket variation AND corr high => C=f(N/n) (closure path).")
    print("         if within-bucket spread ~ overall spread => C NOT determined by N/n => deep-structure wall.")
