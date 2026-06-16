#!/usr/bin/env python3
"""
WF407 / salemzygmund — TAIL + UNIFORMITY probe.

The route (after KB self-refutation) reduces to ONE input:
   (SG)  the per-period value distribution X_zeta(c) = Re(zeta-bar eta_c) is SUB-GAUSSIAN
         with proxy sigma^2 = O(n) UNIFORMLY in (n, m, zeta).
Then union bound over m cosets: P(B >= t) <= 2m exp(-t^2/(2 sigma^2)) gives
   B <= sqrt(2 sigma^2 log m) = O(sqrt(n log m)) = the prize.

What we test here, sharply:
 (A) Does the WORST-direction proxy/n stay bounded as m => infinity at FIXED n?
     (this is the uniformity-over-chars residual; the union bound's m factor is harmless
      ONLY if proxy doesn't grow with m).
 (B) The actual TAIL: empirical P(|eta_c| >= t). Is -log P(>=t) >= t^2/(2 C n) with a
     UNIVERSAL C? Compare the tail decay rate to the Gaussian t^2/(2n) and to the random
     control. A sub-Gaussian tail (rate ~ t^2) vs a fatter (e.g. exponential, rate ~ t) tail
     is the make-or-break.
 (C) The Salem-Zygmund max over a LONG m sweep at fixed n: is B/sqrt(n log m) bounded
     with NO upward trend in m?  (a trend would mean proxy grows with m => route fails).
"""
import cmath, math, random, statistics as st

def is_prime(n):
    if n<2: return False
    for d in range(2,int(n**0.5)+1):
        if n%d==0: return False
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; fac=[]; t=phi; d=2
    while d*d<=t:
        if t%d==0:
            fac.append(d)
            while t%d==0: t//=d
        d+=1
    if t>1: fac.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def gauss_periods(p,n,g=None):
    m=(p-1)//n
    if g is None: g=primitive_root(p)
    gen=pow(g,m,p)
    mu=[]; x=1
    for _ in range(n): mu.append(x); x=(x*gen)%p
    e=[cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas=[]; bc=1
    for c in range(m):
        s=0j
        for x in mu: s+=e[(bc*x)%p]
        etas.append(s); bc=(bc*g)%p
    return etas,m,g

def worst_proxy_over_n(etas,n):
    """worst-direction sub-Gaussian proxy / n via MGF, several lambda."""
    dirs=[cmath.exp(2j*math.pi*t/24) for t in range(24)]
    lambdas=[0.25,0.5,0.75,1.0,1.25,1.5,2.0]
    worst=0.0
    for zeta in dirs:
        X=[(zeta.conjugate()*e).real for e in etas]
        mu=st.mean(X); Xc=[x-mu for x in X]
        for lam in lambdas:
            M=st.mean(math.exp(lam*x) for x in Xc)
            need=2*math.log(M)/(lam*lam) if M>0 else 0.0
            worst=max(worst,need)
    return worst/n

def tail_rate(etas,n,thresholds):
    """For each threshold t (in units of sqrt(n)), empirical P(|eta|>=t*sqrt(n)),
    and the implied tail constant C s.t. P = exp(-t^2/(2C)) (so C = t^2 / (2 (-log P)))."""
    m=len(etas)
    mags=[abs(e) for e in etas]
    out=[]
    for tt in thresholds:
        thr=tt*math.sqrt(n)
        cnt=sum(1 for x in mags if x>=thr)
        P=cnt/m
        if 0<P<1:
            C = (tt*tt)/(2*(-math.log(P)))  # if tail = exp(-(t sqrt n)^2/(2 C n)) = exp(-t^2/(2C))
        else:
            C=float('nan')
        out.append((tt,P,C))
    return out

def main():
    random.seed(7)
    print("=== (A)+(C) FIXED n, growing m: proxy/n and B/sqrt(n log m) trend ===")
    for n in [8,16,32]:
        print(f"\n n={n}:")
        print(f"   {'p':>7} {'m':>6} | {'B':>8} {'B/sqrt(n logm)':>14} | {'worst_proxy/n':>13}")
        p=n+1; rows=0
        ms=[]
        while rows<10:
            p+=n
            if p>200000: break
            if is_prime(p) and (p-1)%n==0:
                m=(p-1)//n
                if m<8: continue
                if m*n>200000: break
                etas,m,g=gauss_periods(p,n)
                B=max(abs(e) for e in etas)
                target=math.sqrt(n*math.log(m))
                wp=worst_proxy_over_n(etas,n)
                print(f"   {p:>7} {m:>6} | {B:8.3f} {B/target:14.3f} | {wp:13.3f}")
                ms.append((m,B/target,wp)); rows+=1
        if len(ms)>=3:
            # crude trend: correlation of (B/target) with log m
            import math as _m
            xs=[_m.log(a[0]) for a in ms]; ys=[a[1] for a in ms]
            mx=st.mean(xs); my=st.mean(ys)
            cov=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
            vx=sum((x-mx)**2 for x in xs)
            slope=cov/vx if vx>0 else 0
            wps=[a[2] for a in ms]
            print(f"   => slope of (B/target) vs log m = {slope:+.4f}  (~0 means NO trend = route OK)")
            print(f"   => worst_proxy/n  range [{min(wps):.3f}, {max(wps):.3f}]  (bounded = route OK)")

    print("\n=== (B) TAIL: empirical P(|eta|>=t sqrt(n)) and implied sub-Gaussian C ===")
    print("   (sub-Gaussian => tail const C bounded across t; growing C with t => fatter tail)")
    thresholds=[1.0,1.5,2.0,2.5,3.0]
    for (p,n) in [(40009,8),(160001,16)]:
        # pick a real prime = 1 mod n with large m
        if not (is_prime(p) and (p-1)%n==0):
            # find nearest
            q=p - (p-1)%n
            while not (is_prime(q) and (q-1)%n==0): q-=n
            p=q
        if p*1>400000:
            continue
        etas,m,g=gauss_periods(p,n)
        print(f"\n  p={p} n={n} m={m}: B={max(abs(e) for e in etas):.3f}")
        print(f"   {'t(xsqrt n)':>11} {'P(>=)':>10} {'-log P':>8} {'impliedC':>9}")
        for tt,P,C in tail_rate(etas,n,thresholds):
            lp = -math.log(P) if 0<P<1 else float('inf')
            print(f"   {tt:>11.1f} {P:>10.5f} {lp:>8.3f} {C:>9.3f}")

if __name__=="__main__":
    main()
