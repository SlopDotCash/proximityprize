#!/usr/bin/env python3
"""
C066 structural confirmation (#407).

Two precise checks:

(S1)  VERIFY the Fourier-duality |T_h| = |A_h|/(m*sqrt(p)) exactly, where A_h is the DFT
      spectrum of |eta_b|^2.  If exact, then (|T_h|)_h and (|eta_c|^2)_c are a DFT pair up to
      the flat constant m*sqrt(p) -- i.e. the T_h family is literally the power spectrum of
      the Gauss-period family. There is no separate 'surface'.

(S2)  Does an MGF/tail bound on T_h give the eta tail MORE CHEAPLY than the eta-MGF itself?
      Parseval ties:  sum_c |eta_c|^2 = constant (= n*m for the family),  and
      max_c |eta_c|^2 <= (1/m) sum_h |A_h| = sqrt(p) * sum_h |T_h|  (triangle, the DFT inversion).
      So an l1 bound on T (sum_h |T_h| small) WOULD bound B.  Measure the l1 mass
      L1 := sum_{h!=0}|T_h| and compare sqrt(p)*L1/m to B^2: is the T-route's natural bound
      (l1 of Jacobi-averages) tight, or is it LOSSY (>> B^2, i.e. weaker than knowing B)?
      A lossy l1 means controlling the Jacobi average is HARDER than controlling B directly.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def run(p,n):
    m=(p-1)//n
    g=primitive_root(p)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    dlog=[0]*p; cur=1
    for k in range(p-1):
        dlog[cur]=k; cur=(cur*g)%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    def eta(c):
        b=pow(g,c,p); return sum(psi((b*w)%p) for w in mu)
    etas=[eta(c) for c in range(m)]
    # Gauss sums tau_j
    tau=[sum(chi_pow(j,x)*psi(x) for x in range(1,p)) for j in range(m)]
    # A_h = sum_j tau_j conj(tau_{j+h})
    A=[sum(tau[j]*tau[(j+h)%m].conjugate() for j in range(m)) for h in range(m)]
    def T(h): return sum(chi_pow(h,(1-w)%p) for w in mu)
    Th=[T(h) for h in range(m)]
    sp=math.sqrt(p)
    # (S1) |T_h| = |A_h|/(m*sqrt(p)) for h!=0
    errS1=max(abs(abs(Th[h]) - abs(A[h])/(m*sp)) for h in range(1,m)) if m>1 else 0.0
    B=max(abs(e) for e in etas); B2=B*B
    # (S2) l1 mass of T (h!=0) and the implied bound sqrt(p)*L1/m on (B^2 - mean)
    L1=sum(abs(Th[h]) for h in range(1,m))
    bound_B2 = sp*L1/m + n  # max|eta|^2 <= (1/m)(A_0 + sum_{h!=0}|A_h|) ; A_0=m*n exactly => mean n
    return dict(p=p,n=n,m=m,errS1=errS1,B2=B2,
                L1=L1, bound_B2=bound_B2, looseness=bound_B2/B2)

def proper_primes(n,count,start_k=8):
    out=[]; k=start_k
    while len(out)<count:
        p=k*n+1
        if k>=8 and sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("# C066 structural: (S1) T_h = power-spectrum of eta;  (S2) l1-of-Jacobi bound looseness\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'errS1(dual)':>11} | {'B^2':>8} {'L1(T)':>9} "
          f"{'bound(B^2)':>10} {'looseness':>9}")
    for n in [8,16,32]:
        for p in proper_primes(n,5,start_k=8)+proper_primes(n,2,start_k=200):
            if p>120000: continue
            r=run(p,n)
            print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['errS1']:>11.2e} | "
                  f"{r['B2']:>8.2f} {r['L1']:>9.2f} {r['bound_B2']:>10.2f} {r['looseness']:>9.2f}")
    print("\nS1=0 => |T_h| is EXACTLY the (normalized) power spectrum of the Gauss periods: same object.")
    print("S2 looseness >> 1 (and GROWING) => the natural l1-of-Jacobi-average bound is LOSSY:")
    print("controlling T_h's mass is STRICTLY HARDER than controlling B directly (route not weaker).")
