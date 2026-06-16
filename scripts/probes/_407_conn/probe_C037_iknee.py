#!/usr/bin/env python3
"""
C037 probe: are the granularity ladder (delta*=e/n, Lambda linear) and the KKH26
march (delta*=1-r/2^mu, super-poly) the SAME monotone I(delta) curve below/above a
single super-polynomial knee?  And is the prize the unmapped knee region?

We test the connection's CONCRETE claim:
  I(delta) := worst-case # of bad scalars gamma at radius delta, for a FIXED code C
  on a smooth (proper-subgroup) domain.  Claim: one monotone I(delta) whose low end
  is the ladder count (~e) and whose high end is the march count (super-poly), with
  delta* = sup{delta : I(delta) <= n=q*eps*} sitting at a single "knee".

PRIZE REGIME: dyadic mu_n, n=2^mu PROPER subgroup of F_q*, q prime = 1 mod n, n << sqrt(q).

Method (exact integer arithmetic, small n):
 We do NOT brute-force over all (u0,u1) at prize q (infeasible). Instead we test the
 STRUCTURE of the connection's two pinned counts directly:
   ladder good-side cap : Lambda_ladder(delta) <= floor(delta*n)+1, valid only while
        the distance condition holds: 3*(floor(delta*n)-? ) ... actually the in-tree
        cap is "<= j whenever delta*n<j and NoWeightLE(3(j-1))" i.e. valid e<=(n-k)/3.
   march good-side cap  : #bad <= C(n,r)/r at radius 1-r/n for the dim-(r-1) code.
 The decisive question: for ONE fixed code (fixed k), do these two caps describe the
 SAME I(delta), i.e. does the march cap apply to the SAME dimension the ladder pins?
"""
import math
from math import comb

def ladder_cap(e):
    # worst-case #bad at radius just below e/n : Lambda(e)=e (proven e..e+1 spike)
    return e

def ladder_valid_e(n, k):
    # distance cond 3(e-1)+k <= n  => e <= (n-k)/3 + 1
    return (n - k)//3 + 1

def march_cap(n, r):
    # #bad <= C(n,r)/r  at radius 1 - r/n for the dimension-(r-1) code (d=r-2)
    return comb(n, r)//r

def march_dim(r):
    # KKH26 march pins delta*=1-r/2^mu for the code of DIMENSION r-1 (degree d=r-2)
    return r - 1

print("="*78)
print("C037: granularity ladder vs KKH26 march -- same I(delta) curve?")
print("="*78)

# ---- TEST 1: do the two pins describe the SAME code (same dimension k)? ----
print("\n[TEST 1] Which code (dimension k) does each staircase pin?")
print("-"*78)
for mu in [3,4,5,6]:
    n = 2**mu
    print(f"\n n=2^{mu}={n}")
    print("  ladder: pins delta*=e/n for ANY fixed k, e<=(n-k)/3, on a budget band")
    print("          (the dimension k is a FREE parameter; delta*<=(n-k)/(3n)<1-rho)")
    print("  march : pins delta*=1-r/n for dimension k=r-1 ONLY (one code per rung r)")
    for r in range(2, n//2+1):
        kmar = march_dim(r)              # = r-1
        dstar_march = 1 - r/n
        # ladder reach FOR THAT SAME dimension k=r-1:
        emax = ladder_valid_e(n, kmar)
        dstar_ladder_max = emax/n
        rho = kmar/n
        johnson = 1 - math.sqrt(rho)
        print(f"   r={r:2d}: march code k={kmar:2d} rho={rho:.3f}  "
              f"delta*_march={dstar_march:.3f}  ladder-reach(same k)<= {dstar_ladder_max:.3f}"
              f"  johnson={johnson:.3f}  marchC(n,r)/r={march_cap(n,r)}")

# ---- TEST 2: the "knee" -- is I(delta) one monotone curve, knee = where it=budget? ----
print("\n"+"="*78)
print("[TEST 2] The knee: locate delta where the count first exceeds budget n=q*eps*")
print("-"*78)
# prize: eps*=2^-128, q ~ n*2^128 so budget q*eps* ~ n. Use budget B = n (order of n).
# For a FIXED dimension k, the in-tree pieces give a count at each radius:
#   - ladder region: I(delta) ~ e = floor(delta*n)   (linear, valid e<=(n-k)/3)
#   - above ladder saturation: NO in-tree count for this k except the march, but the
#     march count C(n,r)/r is at radius 1-r/n and pins the dim-(r-1) code, a DIFFERENT k.
# So for a FIXED k we test whether anything in-tree continues I(delta) past saturation.
for mu in [5]:
    n = 2**mu
    for k in [n//2, n//4]:
        rho = k/n
        budget = n  # ~ q*eps* in prize
        print(f"\n n={n} k={k} rho={rho:.3f} budget(q*eps*~n)={budget}")
        sat_e = ladder_valid_e(n, k)          # last ladder rung
        print(f"  ladder saturates at e={sat_e} -> delta*={sat_e/n:.3f}"
              f"  (=(n-k)/(3n)={ (n-k)/(3*n):.3f}); Johnson 1-sqrt(rho)={1-math.sqrt(rho):.3f}")
        # the march that pins THIS k: need r-1=k => r=k+1
        r_for_k = k+1
        if r_for_k <= n:
            dstar_march = 1 - r_for_k/n
            cap = march_cap(n, r_for_k)
            print(f"  march for THIS dim k: r=k+1={r_for_k}, delta*=1-{r_for_k}/{n}={dstar_march:.3f},"
                  f" cap C(n,{r_for_k})/{r_for_k}={cap}")
            print(f"    -> is march delta* ABOVE Johnson? {dstar_march:.3f} vs {1-math.sqrt(rho):.3f}:"
                  f" {'YES (in window)' if dstar_march>1-math.sqrt(rho) else 'NO'}")
            print(f"    -> march cap {cap} vs budget {budget}: "
                  f"{'EXCEEDS budget (bad side)' if cap>budget else 'within budget'}")
        # Is there a knee region BETWEEN ladder reach and march radius, for this fixed k?
        print(f"  KNEE GAP for fixed k={k}: ladder reaches delta={sat_e/n:.3f},"
              f" march(this k) is AT delta={1-r_for_k/n:.3f}")
        print(f"    region ({sat_e/n:.3f}, {1-r_for_k/n:.3f}) has NO in-tree count for this code")
