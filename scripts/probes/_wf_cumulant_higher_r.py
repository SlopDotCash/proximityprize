#!/usr/bin/env python3
"""
#407 cumulant-from-flatness, HIGHER r: does the autocorrelation R(h)=conj(tau_h)T_h/p
give an UPPER bound on P_{2r} (the DFT 2r-moment) that BEATS the Markov-Krein wall?

The Markov-Krein wall says: from the PROVEN char-0 moments E_1..E_R (R~3 provable), the
sharp atom bound is m^{1/2R}*sqrt(n) -- never sqrt(n log m). The moment route is short by
Theta(log m) PROVEN moments.

NEW QUESTION (the autocorrelation lever): we have the EXACT autocorrelation
   R(h) = conj(tau_h) T_h / p,   |R(h)| = |T_h|/sqrt(p).
The DFT moment P_{2r} expands as a sum over closed (h_1+...+h_r = h_1'+...+h_r') walks of
products of R. The DIAGONAL (perfect matchings: pair each h_i with an h_j') gives exactly
(2r-1)!! R(0)^r m^r = (2r-1)!! m^r (the Gaussian value). The OFF-DIAGONAL (non-matching
walks) is the defect. The KEY: each off-diagonal term is a product of r autocorrelation
values R(h_i) with sum of args = 0; by I3 EACH |R(h)| = |T_h|/sqrt(p), and the count of
non-degenerate walks is controlled by HIGHER tangent moments.

We TEST whether a CONVOLUTION/Young bound on the autocorrelation gives a real upper bound:
  P_{2r} = m^r * sum over closed r-walks of prod R.  In particular P_4 = m^2 sum_h |R(h)|^2.
  P_6 = m^3 sum_{h1,h2} R(h1)R(h2)conj(R(h1+h2))  (the bispectrum / triple correlation).
  HYPOTHESIS to test: |P_6 - 15 m^3| <= (combinatorial defect from off-diagonal triple-corr).

CRUX TEST: is sum_{h1,h2}|R(h1)R(h2)R(h1+h2)| (the L1 bispectrum) small enough to bound P_6?
Compare:  P_6_diag = 15 m^3 (target);  P_6_actual;  P_6_L1bound = m^3 * sum_{h1,h2}|RRR|.
If the L1 bound TRACKS 15 m^3 (not m^{?} larger) then the autocorrelation gives the cumulant
WITHOUT needing extra proven moments -- a potential ESCAPE from Markov-Krein. If L1 >> target,
the off-diagonal cancellation (phases of R = phases of T_h) is ESSENTIAL and the autocorr L1
route fails exactly like the triangle bound (5b).
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def run(p,n,rmax=3):
    m=(p-1)//n
    g=primitive_root(p)
    dlog=[0]*p;cur=1
    for k in range(p-1): dlog[cur]=k; cur=cur*g%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    tau=[sum(chi_pow(j,x)*psi(x) for x in range(1,p)) for j in range(m)]
    a=[t/math.sqrt(p) for t in tau]
    def R(h): return sum(a[j]*a[(j+h)%m].conjugate() for j in range(m))/m
    Rh=[R(h) for h in range(m)]
    # DFT
    def D(c): return sum(a[j]*cmath.exp(-2j*math.pi*(j*c)/m) for j in range(m))
    Ds=[D(c) for c in range(m)]
    P={r: sum(abs(d)**(2*r) for d in Ds)/m for r in range(1,rmax+1)}
    # target Gaussian diagonal value (2r-1)!! m^r
    def dfac2(r):
        x=1
        for i in range(1,r+1): x*=(2*i-1)
        return x
    tgt={r: dfac2(r)*m**r for r in range(1,rmax+1)}
    # P_4 = m^2 sum_h |R|^2 ;  L1 bound for P_4 = same (already |.|). diag target 3 m^2.
    P4_L1 = m**2 * sum(abs(Rh[h])**2 for h in range(m))     # = exact P4
    # P_6: triple correlation. exact via DFT already in P[3].
    # L1 bispectrum bound: P_6 <= m^3 * sum_{h1,h2} |R(h1)||R(h2)||R(h1+h2)|  ??? check sign.
    # Actually P_6 = (1/m) sum_c |D|^6. |D|^2 = m sum_h R(h) e^{-2pi i hc/m}.
    # |D|^6 = m^3 sum_{h1,h2,h3} R(h1)R(h2)R(h3) e^{-2pi i(h1+h2+h3)c/m}; (1/m)sum_c picks h1+h2+h3=0:
    # P_6 = m^3 sum_{h1,h2} R(h1)R(h2)R(-h1-h2).  L1 = m^3 sum_{h1,h2}|R(h1)R(h2)R(h1+h2)|.
    L1_6=0.0
    for h1 in range(m):
        for h2 in range(m):
            L1_6 += abs(Rh[h1])*abs(Rh[h2])*abs(Rh[(-h1-h2)%m])
    P6_L1 = m**3 * L1_6
    P6_actual = P[3]
    P6_tgt = tgt[3]
    # ratios
    return dict(p=p,n=n,m=m,
                P4=P[2],P4_tgt=tgt[2],
                P6=P6_actual,P6_tgt=P6_tgt,P6_L1=P6_L1,
                r46=P[2]/tgt[2], r66=P6_actual/P6_tgt,
                L1_over_tgt6 = P6_L1/P6_tgt,
                L1_over_actual6 = P6_L1/P6_actual)

def find_primes(n,count,start=2,cap=4000):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407 HIGHER-r: does L1 autocorrelation (bispectrum) bound P_6 near the 15 m^3 target?\n")
    print(f"{'p':>5}{'n':>4}{'m':>4} | {'P4/tgt':>7}{'P6/tgt':>7} | {'L1_6/tgt':>9}{'L1_6/act':>9}")
    for n in [4,8,16,32]:
        ps=find_primes(n,4)+find_primes(n,1,start=20)
        for p in sorted(set(ps)):
            if p>1500: continue
            r=run(p,n)
            print(f"{p:>5}{n:>4}{r['m']:>4} | {r['r46']:>7.3f}{r['r66']:>7.3f} | "
                  f"{r['L1_over_tgt6']:>9.2f}{r['L1_over_actual6']:>9.2f}")
    print("\nP6/tgt ~1 = the cumulant is Gaussian at r=3 (good).")
    print("L1_6/tgt: if ~1, the L1 bispectrum CERTIFIES P_6<=O(tgt) WITHOUT phase cancellation (ESCAPE).")
    print("         if >>1 and GROWING in m, the off-diagonal phase cancellation is essential (route walls).")
