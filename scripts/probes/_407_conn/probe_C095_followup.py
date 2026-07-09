#!/usr/bin/env python3
"""
probe_C095_followup.py  (#407 C095)  -- chase the TEST1 surprise + settle the Betti claim.

TEST1 showed chi^h(1-w^{-1}) = chi^h(1-w) EXACTLY for all w (frac mult==1 was 1.000).
REASON to verify: in TangentSumJacobiAverage.lean the character chi has mu_n = ker chi
(chi has order m=(p-1)/n, mu_n = order-n subgroup = ker chi). The multiplier chi^h(-w^{-1})
has -w^{-1} in mu_n = ker chi, so chi^h(-w^{-1}) = 1 TRIVIALLY. So the "involution" makes
the two terms (w, w^{-1}) EQUAL -- but that is NOT the prize object.

CRITICAL DISTINCTION the connection conflates:
  (a) chi^h with chi of order m, mu_n = ker chi:  this is the JACOBI-AVERAGE T_h in the .lean file.
      For this chi, chi^h is TRIVIAL on mu_n, so T_h has REAL structure but the involution gives
      chi^h(1-w^{-1})=chi^h(1-w): the n-1 terms come in EQUAL pairs {w,w^{-1}} (involution w|->w^{-1}),
      so T_h IS a sum over n/2 orbits each weight 2 (plus fixed pts w=+-1). THIS halving is real
      for the *number of summands*, but it does NOT change the DEGREE of the curve / the Betti
      number governing the MOMENT growth (E_r), which is what gates the prize bound.
  (b) the GAUSS-PERIOD / moment object: B = max_b |eta_b|, eta_b = sum_{x in mu_n} psi(bx).
      Its moment E_r(mu_n) is the Fermat-curve point count. THIS is the prize-gating quantity,
      and TEST3 already measured it directly (no Betti halving -- 2-power E_r >= odd E_r, Wall-G).

So we test the SHARP version of C095's *actual* claim chain:
  (1) Confirm: T_h (Jacobi-average chi) = sum over n/2 involution orbits, each pair EQUAL.
      => |T_h| is literally a sum of (n-2)/2 doubled complex terms + fixed points. Does this
         halve the CURVE DEGREE in any moment-relevant sense? Test: does the autocorrelation
         R_T(k) / the 2r-th moment of (T_h)_h drop to the deg-(n/2) Hasse-Weil value?
  (2) The DECISIVE one: does the 2r-th moment of the tangent sequence T_h itself (sum_h |T_h|^{2r})
      grow like a degree-(n/2) curve count (Betti halved) or a degree-n one?
      Compare sum_h |T_h|^{2r} to n-curve and (n/2)-curve Gaussian predictions.
  (3) Re-confirm the prize-relevant object eta_b moment is UNCHANGED (TEST3 control) -- the
      "halving" lives only on the term-COUNT of T_h, not on E_r, so r* does NOT move.
"""
import math, cmath
from collections import Counter

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
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

def primitive_root(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        s=set(); x=1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    return None

def setup(p,n):
    g0=primitive_root(p); mu=subgroup(p,n); m=(p-1)//n
    dlog={}; x=1
    for k in range(p-1): dlog[x]=k; x=x*g0%p
    return g0,mu,m,dlog

def T_h(p,n,hexp,mu,m,dlog):
    wm=cmath.exp(2j*math.pi/m)
    def chi_h(y):
        y%=p
        if y==0: return 0j
        return wm**((hexp*dlog[y])%m)
    return sum(chi_h((1-w)%p) for w in mu if w!=1)

def involution_orbit_structure(p,n,mu):
    """confirm the n-1 nonzero terms pair up under w<->w^{-1}; count fixed points (w=+-1)."""
    seen=set(); pairs=0; fixed=0
    for w in mu:
        if w==1: continue
        winv=pow(w,p-2,p)
        if w in seen: continue
        if winv==w: fixed+=1; seen.add(w)
        else:
            pairs+=1; seen.add(w); seen.add(winv)
    return pairs, fixed

def energy_Er(p,n,r,mu):
    cur=Counter({0:1})
    for _ in range(r):
        nxt=Counter()
        for s,c in cur.items():
            for a in mu: nxt[(s+a)%p]+=c
        cur=nxt
    return sum(c*c for c in cur.values())

if __name__=="__main__":
    print("# C095 follow-up: separate the (real) term-count halving from the (claimed) Betti/degree halving\n")

    print("="*86)
    print("PART 1: involution orbit structure of T_h (Jacobi-average chi, mu_n=ker chi)")
    print("  Confirms terms pair w<->w^{-1} with chi^h(1-w)=chi^h(1-w^{-1}) (mult=1, TEST1).")
    print("  => T_h = sum over (n-2)/2 EQUAL pairs + fixed pts.  Real, but only on term COUNT.")
    print("="*86)
    print(f"{'p':>7} {'n':>4} | {'#orbit pairs':>12} {'#fixed':>7} {'check 2*pairs+fixed':>20} (== n-1?)")
    for n in [8,16,32,64]:
        cnt=0;k=2
        while cnt<2:
            p=k*n+1;k+=1
            if p>60000:break
            if is_prime(p) and p>n*n:
                mu=subgroup(p,n)
                pr,fx=involution_orbit_structure(p,n,mu)
                print(f"{p:>7} {n:>4} | {pr:>12} {fx:>7} {2*pr+fx:>20} ({n-1})")
                cnt+=1

    print()
    print("="*86)
    print("PART 2 (DECISIVE): 2r-th moment of the TANGENT sequence  M_r := sum_{h} |T_h|^{2r}")
    print("  If the involution HALVES the curve degree (Betti/2), M_r should track a deg-(n/2)")
    print("  Hasse-Weil count, NOT a deg-n one. Compare normalized growth.")
    print("  We report M_r / m^{?}: the diagonal/Gaussian scale is m * (Gaussian E_r-like).")
    print("  Direct test: ratio of consecutive moments  M_{r}/M_{r-1}  -- a degree-(n) sequence")
    print("  has a characteristic growth; a halved degree would grow slower. Compare to E_r ratios.")
    print("="*86)
    for n in [8,16]:
        p=None;k=2
        while True:
            cand=k*n+1;k+=1
            if cand>n*n*4 and is_prime(cand) and cand>n*n: p=cand;break
            if cand>200000:break
        if p is None: continue
        g0,mu,m,dlog=setup(p,n)
        # full tangent sequence over all h in 0..m-1
        Ts=[T_h(p,n,h,mu,m,dlog) for h in range(m)]
        absT2=[abs(t)**2 for t in Ts[1:]]   # h!=0 (h=0 gives T_0=n-1, the spike)
        print(f"\n  n={n} p={p} m={m}")
        print(f"    {'r':>2} {'M_r=sum_h|T_h|^2r':>20} {'M_r/M_{r-1}':>13} {'E_r(mu_n)':>14} {'E_r/E_{r-1}':>12}")
        prevM=None; prevE=None
        for r in range(1,6):
            Mr=sum(a**r for a in absT2)
            Er=energy_Er(p,n,r,mu)
            mr_ratio = (Mr/prevM) if prevM else float('nan')
            er_ratio = (Er/prevE) if prevE else float('nan')
            print(f"    {r:>2} {Mr:>20.1f} {mr_ratio:>13.3f} {Er:>14} {er_ratio:>12.3f}")
            prevM=Mr; prevE=Er
        print("    NOTE: if Betti halved, |T_h| would be sqrt(n/2)-flat not sqrt(n)-flat:")
        maxT=max(abs(t) for t in Ts[1:])
        avgT=sum(abs(t) for t in Ts[1:])/(m-1)
        print(f"    max|T_h|={maxT:.3f}  sqrt(n)={math.sqrt(n):.3f}  sqrt(n/2)={math.sqrt(n/2):.3f}  "
              f"avg|T_h|={avgT:.3f}")
        print(f"    max|T_h|/sqrt(n)={maxT/math.sqrt(n):.3f}   max|T_h|/sqrt(n/2)={maxT/math.sqrt(n/2):.3f}")
