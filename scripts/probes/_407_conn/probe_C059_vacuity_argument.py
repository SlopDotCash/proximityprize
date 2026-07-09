#!/usr/bin/env python3
"""
C059 part 3: the DECISIVE structural test of usefulness.

C059 bound:  anomaly  <=  R_r(0) * #{contributing cyclotomic states alpha!=0, p|N(alpha)}.
Facts to pin (exact):
  (1) R_r(0) == E_r^{Fp}  (the autocorr-at-origin IS the whole char-p energy).        [verified parts 1-2]
  (2) anomaly <= E_r^{Fp}  ALWAYS, trivially (anomaly = E_Fp - E0 <= E_Fp since E0>=0). [trivial]
  (3) Therefore the C059 bound is NON-VACUOUS (strictly better than (2)) iff
          R_r(0) * #contrib  <  E_r^{Fp} = R_r(0),  i.e.  #contrib < 1, i.e. #contrib == 0.
      When #contrib >= 1 the C059 bound is >= R_r(0) = E_Fp >= anomaly => WEAKER than trivial.
  (4) #contrib == 0  <=>  clean range (no spurious tuple)  <=>  no_spurious_tuple_of_lt_prime
      already gives anomaly == 0 with NO use of the autocorr brick.

So: the autocorr per-point cap R_r(z)<=R_r(0) contributes NOTHING to bounding the anomaly,
because the cap value equals the entire energy. The only genuinely informative input is the
COUNT #contrib (Bourgain-Shkredov equidistribution), which C059 leaves open and merely multiplies
by a vacuous cap.

This script demonstrates (3) by FORCING a contributing state to exist (synthetic prime that
divides a known norm), then showing bound >= E_Fp > anomaly.
"""
import math
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def char0_sumr(n, r):
    half=n//2
    def coord(e):
        e%=n; v=[0]*half
        if e<half: v[e]+=1
        else: v[e-half]-=1
        return tuple(v)
    f=Counter()
    for e in range(n): f[coord(e)]+=1
    def conv(a,b):
        c=Counter()
        for x,ax in a.items():
            for y,by in b.items():
                c[tuple(p+q for p,q in zip(x,y))]+=ax*by
        return c
    s=Counter({tuple([0]*half):1})
    for _ in range(r): s=conv(s,f)
    return s, half

def norm_of_state(v, n):
    """N(alpha) = Res(Phi_n, g) = prod over primitive n-th roots omega of g(omega), for alpha=sum c_j zeta^j.
       Compute exactly via complex eval at primitive roots, round to nearest int."""
    import cmath
    half=len(v)
    prod=1.0+0j
    # primitive n-th roots of unity: zeta^k for gcd(k,n)=1
    for k in range(n):
        if math.gcd(k,n)!=1: continue
        w=cmath.exp(2j*math.pi*k/n)
        val=sum(c*(w**j) for j,c in enumerate(v))
        prod*=val
    return round(prod.real)

def demo(n, r):
    sumr, half = char0_sumr(n, r)
    E0=sum(c*c for c in sumr.values())
    # build the difference-state -> mass, and their integer norms
    supp=list(sumr.items())
    diff=Counter()
    for s,cs in supp:
        for t,ct in supp:
            d=tuple(a-b for a,b in zip(s,t))
            diff[d]+=cs*ct
    # nonzero states with their norms
    state_norm={}
    for d,mass in diff.items():
        if all(x==0 for x in d): continue
        if mass==0: continue
        Nd=norm_of_state(d,n)
        state_norm[d]=(mass,Nd)
    # pick a prime q | N(alpha) for some nonzero state with smallest |N|>1 -> a FORCED contributor
    cand=None
    for d,(mass,Nd) in sorted(state_norm.items(), key=lambda kv: abs(kv[1][1])):
        if abs(Nd)<=1: continue
        # smallest prime factor of |Nd|
        m=abs(Nd); pf=None
        f=2
        while f*f<=m:
            if m%f==0: pf=f; break
            f+=1
        if pf is None: pf=m
        cand=(d,mass,Nd,pf); break
    print(f"  n={n} r={r}: E0={E0}  #nonzero-diff-states={len(state_norm)}")
    if cand:
        d,mass,Nd,pf=cand
        print(f"    forced contributor: state norm N(alpha)={Nd}, smallest-prime-factor q={pf}, its diff-mass={mass}")
        print(f"    => at q={pf}: #contrib >= 1, and EACH contributing state has diff-mass <= R0 by autocorr cap (mass={mass} <= R0=E_Fp)")
        print(f"    => C059 bound R0*#contrib >= R0 = E_Fp >= anomaly  => bound is WEAKER than the trivial 'anomaly <= E_Fp'.")
        # numeric: at this q the actual anomaly equals sum of masses of ALL states whose norm is divisible by q
        anomaly_at_q=sum(mass2 for (d2,(mass2,N2)) in state_norm.items() if N2%pf==0)
        ncontrib=sum(1 for (d2,(mass2,N2)) in state_norm.items() if N2%pf==0)
        # R0 = E_Fp ~ E0 (clean) + anomaly; at small q E_Fp could differ, but R0 >= E0 always and >= anomaly.
        print(f"    actual anomaly at q={pf}: {anomaly_at_q}  (over {ncontrib} contributing states)")
        print(f"    autocorr-cap bound at q={pf}: E_Fp_est(>=E0={E0}) * {ncontrib} >= {E0*ncontrib}  >> anomaly {anomaly_at_q}")
        print(f"    looseness factor >= {E0*ncontrib/max(anomaly_at_q,1):.3e}")
    print()

if __name__=="__main__":
    print("=== C059 part3: decisive vacuity of the autocorr cap for bounding the anomaly ===\n")
    print("Structural fact: R_r(0) = E_r^Fp (whole energy). So cap*count is non-vacuous ONLY at count=0 (clean range).\n")
    for (n,r) in [(8,2),(8,3),(16,2),(16,3)]:
        demo(n,r)
    print("CONCLUSION: the autocorr per-point cap value = the entire char-p energy, so multiplying by")
    print("any count>=1 gives a bound >= E_Fp >= anomaly (weaker than trivial). Non-vacuous only when")
    print("count=0 = the clean range already discharged by no_spurious_tuple_of_lt_prime ALONE.")
    print("The brick-fusion adds nothing; the open input #contrib (Bourgain-Shkredov) is untouched.")
