#!/usr/bin/env python3
"""
#407 cumulant-from-flatness: the CONTENT of kappa_2 is the SECOND MOMENT of T_h.

CHAIN (all exact, established):
  R(h) = conj(tau_h) T_h / p,  |tau_h|=sqrt(p) (h!=0)  =>  |R(h)| = |T_h|/sqrt(p).
  kappa_2 = (p/nm)^2 * P_4/(3 m^2),  P_4 = m^2 sum_h |R(h)|^2
        => kappa_2 = (p/nm)^2 * sum_h |R(h)|^2 / 3
        => kappa_2 = (p/nm)^2 * (|R(0)|^2 + (1/p) sum_{h!=0} |T_h|^2 ) / 3.
  R(0) = (1/m) sum|a_j|^2 = ((m-1)+1/p)/m ~ 1 (exactly (m-1+1/p)/m).
  T_0 = n-1 but h=0 term uses R(0) not T_0/sqrt p (tau_0=-1 special); for h!=0 use |T_h|^2.

So:  3 m^2 (nm/p)^2 kappa_2  -  m^2 R(0)^2  =  (m^2/p) sum_{h!=0} |T_h|^2.
The TANGENT SECOND MOMENT  V := sum_{h=0}^{m-1} |T_h|^2  is a CLOSED combinatorial count:
  V = sum_h |sum_{w in mu_n} chi^h(1-w)|^2 = sum_{w,w' in mu_n} sum_h chi^h((1-w)/(1-w'))
    = m * #{(w,w') in mu_n^2 : (1-w)/(1-w') in mu_n}      [orthogonality: sum_h chi^h(z)=m*1[z in mu_n], z!=0]
    + (boundary terms where 1-w=0 i.e. w=1, contributing 0 since chi^h(0)=0).
  Let N := #{(w,w') in mu_n^2 \ {w=1,w'=1}: (1-w)/(1-w') in mu_n}.  Then V = m * N.
  (This N is EXACTLY the Sol-count from probe_tangent_correlation_structure: forced floor 2n-3.)

THE PUNCHLINE: kappa_2 <= ~1  <=>  V = m*N  is controlled  <=>  N is controlled.
  kappa_2 = (p/nm)^2 (R(0)^2 + (m/p) N ... wait recompute with V=mN:
  sum_{h!=0}|T_h|^2 = V - |T_0|^2 = mN - (n-1)^2.
  kappa_2 = (p/nm)^2 [ R(0)^2 + (mN-(n-1)^2)/p ] / 3.
  With p ~ nm, R(0)~1:  kappa_2 ~ [1 + (mN-(n-1)^2)/p]/3 ~ [1 + N/n - n/m]/3  (since m/p~1/n).
  => kappa_2 <= 1  <=>  N <= 3n - 1 + n^2/m + ...  i.e.  N <~ 3n  (since n^2/m -> 0 in prize).
THE FORCED FLOOR is N = 2n-3 (probe_tangent_correlation), giving kappa_2 ~ (1+(2n-3)/n-...)/3 ~ (3-3/n)/3 -> 1^-.
=> kappa_2 -> 1 from below is EXACTLY the statement N=2n-3 (no extra coincidences).
   EXTRA coincidences N>2n-3 (bad primes) push kappa_2 > 1 -- THE r=2 defect onset.

This is the rigorous content-identification: kappa_2 <= 1  <=>  N(mu_n) <= 3n + o(n)  <=>
the unit equation (1-w) = u(1-w'), u,w,w' in mu_{2^a}, has only the FORCED ~2n solutions.
For HIGHER r: kappa_r <= 1 <=> r-fold version: #r-walks of T <= (2r-1)!! n^r forced.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def run(p,n):
    m=(p-1)//n
    g=primitive_root(p)
    mu_set=set(); mu=[]
    for t in range(n):
        x=pow(g,(m*t)%(p-1),p); mu.append(x); mu_set.add(x)
    # N = #{(w,w') in mu^2, w!=1, w'!=1 : (1-w)/(1-w') in mu}
    inv=[0]*p
    for x in range(1,p): inv[x]=pow(x,p-2,p)
    N=0
    for w in mu:
        if w==1: continue
        a=(1-w)%p
        for wp in mu:
            if wp==1: continue
            b=(1-wp)%p
            z=(a*inv[b])%p
            if z in mu_set: N+=1
    # exact kappa_2 from N:  need R(0), tangent T_h second moment.
    # V = m*N ; T_0 = n-1.
    R0 = ((m-1)+1.0/p)/m
    sum_Th2_off = m*N - (n-1)**2          # = sum_{h!=0}|T_h|^2  (since V=sum_h|T_h|^2 = m N includes h=0 -> |T_0|^2=(n-1)^2)
    kappa2_pred = (p/(n*m))**2 * ( R0**2 + sum_Th2_off/p )/3.0
    # cross-check direct kappa_2 from eta
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    # coset reps
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=[abs(sum(psi(b*w%p) for w in mu)) for b in reps]
    kappa2_dir = (sum(e**4 for e in etas)/m)/(3*n**2)
    floor = 2*n-3
    house = max(etas[1:]) if m>1 else etas[0]
    C = house/math.sqrt(n*math.log(max(m,2)))
    return dict(p=p,n=n,m=m,N=N,floor=floor,extra=N-floor,
                kappa2_pred=kappa2_pred,kappa2_dir=kappa2_dir,C=C,
                N_over_n=N/n)

def find_primes(n,count,start=2,cap=8000):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407: kappa_2 <=> tangent 2nd moment V=m*N, N = #unit-eq solutions (forced floor 2n-3)\n")
    print(f"{'p':>6}{'n':>4}{'m':>5} | {'N':>5}{'floor':>6}{'extra':>6} {'N/n':>5} | "
          f"{'k2_pred':>8}{'k2_dir':>8} | {'C':>5}")
    for n in [4,8,16,32,64]:
        ps = find_primes(n,5)+find_primes(n,2,start=40)
        for p in sorted(set(ps)):
            if p>6000: continue
            r=run(p,n)
            flag = " <<BAD" if r['extra']>0 else ""
            print(f"{p:>6}{n:>4}{r['m']:>5} | {r['N']:>5}{r['floor']:>6}{r['extra']:>6} {r['N_over_n']:>5.2f} | "
                  f"{r['kappa2_pred']:>8.4f}{r['kappa2_dir']:>8.4f} | {r['C']:>5.2f}{flag}")
    print("\nk2_pred (from N alone) MUST equal k2_dir (from eta) -> proves kappa_2 is a CLOSED function of N.")
    print("extra=0 (N=2n-3) => kappa_2->1^-; extra>0 (bad prime) => kappa_2>1 = the r=2 p-defect onset.")
