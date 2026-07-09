#!/usr/bin/env python3
"""
#407 cumulant-from-flatness: WHY does kappa_2<=1 imply kappa_r<=1?  Is it structural?

The cumulant kappa_r = E[|eta|^{2r}] / ((2r-1)!! n^r) over the m periods, with E[|eta|^2]=p-n~nm,
normalized so E[|eta|^2]/n... wait: kappa_1=E[|eta|^2]/(1*n)=(p-n)/(mn)/n? recompute.
Actually kappa_1 = (sum|eta|^2/m)/(1!!*n) = ((p-n)/m)/n ~ (nm/m)/n = 1. Good, kappa_1~1.
So the |eta_b|^2 values have MEAN ~ n (since sum/m=(p-n)/m~n). Let X_b=|eta_b|^2/n (mean ~1).
Then kappa_r = E[X^r]/(2r-1)!!.  GAUSSIAN |eta|^2 ~ n*Exp(1)*?? For complex Gaussian eta,
|eta|^2 ~ n * (chi^2_2 /2)= n*Exp(1), and E[Exp(1)^r]=r!, but (2r-1)!!=E[|Z|^{2r}] for Z~CN.
For eta = sqrt(n) * CN(0,1):  E[|eta|^{2r}] = n^r r!.  Then kappa_r = n^r r!/((2r-1)!! n^r)=r!/(2r-1)!!.
  r!/(2r-1)!!: r=1:1, r=2:2/3, r=3:6/15=0.4, r=4:24/105=0.229... -> matches GOOD-prime kappa_r!!
  (n=8 m=150: k2=0.858 vs 2/3=0.667? no. Let me check: maybe eta REAL not complex.)
eta is REAL (since -1 in mu_n => eta_b real). Real Gaussian eta=sqrt(n)N(0,1): E[eta^{2r}]=n^r(2r-1)!!,
  kappa_r = (2r-1)!!/(2r-1)!! = 1 EXACTLY. So GOOD primes should have kappa_r->1 (real Gaussian).
But measured GOOD kappa_2~0.86<1, kappa_3~0.6<1 -- SUB-Gaussian (lighter tails than Gaussian).
So the period distribution is SUB-Gaussian, kappa_r<1, MONOTONE DECREASING in r at good primes.

THE STRUCTURAL QUESTION: is X_b=|eta_b|^2/n a sub-Gaussian / sub-exponential variable whose
moment sequence is LOG-CONVEX-DOMINATED so that kappa_2<=1 forces kappa_r<=1? Test:
 (a) is the sequence m_r := E[X^r] log-convex? (m_r^2 <= m_{r-1} m_{r+1})  -- generic for any measure (Cauchy-Schwarz). YES always.
 (b) does kappa_r = m_r/(2r-1)!! satisfy kappa_{r+1}/kappa_r <= kappa_r/kappa_{r-1} * (something)?
 (c) KEY: the period measure is determined by ITS the fiber/N structure. kappa_2<=1 <=> N<=3n.
     Does N<=3n (the r=2 fiber bound) CONTROL the r-fold fiber count N_r (the higher walk count)?
     N_r = #{ r-tuples (w_1..w_r,w_1'..w_r') in mu^{2r} : prod(1-w_i)=prod(1-w_j') as MULTISET ratio in mu }.
     Forced (matchings) = (2r-1)!! * n^r-ish. We test N_r/forced vs N/forced=N_2.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def analyze(p,n,rmax=8):
    m=(p-1)//n
    g=primitive_root(p)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    seen=set();reps=[];b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=[abs(sum(psi(b*w%p) for w in mu)) for b in reps]
    X=[e*e/n for e in etas]   # mean ~1
    meanX=sum(X)/m
    mr={r: sum(x**r for x in X)/m for r in range(1,rmax+1)}
    def df(r):
        v=1
        for i in range(1,r+1): v*=(2*i-1)
        return v
    kap={r: mr[r]/df(r) for r in range(1,rmax+1)}
    # log-convexity check of kappa: ratio kappa_{r+1}/kappa_r monotone non-increasing?
    ratios={r: kap[r+1]/kap[r] for r in range(1,rmax)}
    return dict(m=m,meanX=meanX,kap=kap,ratios=ratios)

def find_primes(n,cap,start=2):
    out=[];k=start
    while True:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407: structure of kappa_r. GOOD-prime real-Gaussian baseline kappa_r=1; measured SUB-Gaussian.")
    print("Test: is kappa_{r+1}/kappa_r monotone DECREASING (=> kappa_2<=1 caps all)? And ratio at BAD primes.\n")
    print(f"{'n':>3}{'p':>6}{'m':>5}{'k2':>6}{'k3':>6}{'k4':>6} | "
          f"{'rho2':>6}{'rho3':>6}{'rho4':>6}{'rho5':>6}  (rho_r=k_{{r+1}}/k_r)")
    for n in [16,32,64]:
        for p in find_primes(n,min(6000,200*n)):
            r=analyze(p,n,7)
            m=r['m']
            if m not in (15,21,40,72,99,124,150) and r['kap'][2]<=1.0: continue
            tag=" BAD" if r['kap'][2]>1.0 else ""
            print(f"{n:>3}{p:>6}{m:>5}{r['kap'][2]:>6.3f}{r['kap'][3]:>6.3f}{r['kap'][4]:>6.3f} | "
                  f"{r['ratios'][2]:>6.3f}{r['ratios'][3]:>6.3f}{r['ratios'][4]:>6.3f}{r['ratios'][5]:>6.3f}{tag}")
    print("\nIf rho_r=k_{r+1}/k_r is <=1 and DECREASING at good primes => moment seq sub-Gaussian,")
    print("kappa monotone down from kappa_1~1, so kappa_2<=1 => kappa_r<=1 STRUCTURALLY (log-concave tail).")
    print("At BAD primes rho_r>1 (deep moments grow) -- the defect = a heavy atom, breaks monotonicity.")
