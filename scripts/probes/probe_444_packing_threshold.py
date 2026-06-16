#!/usr/bin/env python3
"""
probe_444_packing_threshold.py  (#444 SEAM A, Task 2)

Re-derive, from scratch, the double-counting / second-moment packing bound the claim invokes,
and locate the exact threshold. Then test whether it excludes the window tau<sqrt(rho).

SETUP per claim:
 - members live as polys over mu_N (N=n/2).  Each member agrees with u on >= s = tau*n points of
   mu_n.  Descended to mu_N: a member's agreement footprint in mu_N has size >= a where
   "a = (2tau - rho)N" per the claim text.  Pairwise intersection (in mu_N) <= w := 2k = 2 rho n
   ... but careful with N vs n normalization.  We reproduce BOTH the claim's stated threshold and
   the correct second-moment bound, symbolically and numerically.

Second-moment (Johnson) packing: L subsets A_1..A_L of a ground set of size M, each |A_i|>=a,
pairwise |A_i∩A_j|<=w.  Then (sum 1_{A_i})^2 counting:
    sum_i |A_i|  <= count of (point, set) incidences
    Cauchy-Schwarz / inclusion:  L*a <= M + (sum over points of (deg choose stuff))...
The standard *Johnson bound* form: a list of codewords pairwise agreeing <= w, each agreeing with
received word on >= a points, has size
    L <= a(M - w) / (a^2 - w M)        [when a^2 > w M]   (the "Johnson denominator" form)
=> finite/bounded L  iff  a^2 > w*M.    THIS is the real packing threshold.

Plug the descent normalization.  Two natural readings:
 (R1) ground = mu_n (M=n), a = s = tau n, w = pairwise overlap bound = 2k = 2 rho n:
        a^2 > w M  <=>  tau^2 n^2 > 2 rho n * n  <=>  tau^2 > 2 rho  <=>  tau > sqrt(2 rho).
 (R2) ground = mu_N (M=N=n/2), descended agreement a=(2tau-rho)N, overlap w=2k=2 rho n=4 rho N:
        a^2 > wM  <=> (2tau-rho)^2 N^2 > 4 rho N * N <=> (2tau-rho)^2 > 4 rho
        <=> 2tau-rho > 2 sqrt(rho) <=> tau > sqrt(rho) + rho/2.   <-- the CLAIM's threshold.
So the claim's threshold tau>sqrt(rho)+rho/2 is reading (R2). We test whether window tau is excluded
under BOTH readings, AND whether the Johnson denominator a^2-wM is positive (=> bound active) at the
window for rho in {1/8,1/16}.
"""
from math import sqrt

def analyze(rho):
    sqrt_rho=sqrt(rho)
    # window: s = round((rho+eta)n), eta=rho => tau = 2 rho (agreement FRACTION over mu_n)
    tau=2*rho
    print(f"\n  rho={rho}  (window agreement fraction tau = 2*rho = {tau:.4f})")
    print(f"    Johnson distance radius 1-sqrt(rho) => agreement-side Johnson radius sqrt(rho)={sqrt_rho:.4f}")
    print(f"    window tau < sqrt(rho)? {tau<sqrt_rho}   (=> window is BEYOND Johnson, list can be super-constant)")
    # reading R1
    thrR1=sqrt(2*rho)
    print(f"    [R1 ground=mu_n] packing active iff tau>sqrt(2 rho)={thrR1:.4f}:  window active? {tau>thrR1}")
    # reading R2 (claim)
    thrR2=sqrt_rho+rho/2
    print(f"    [R2 ground=mu_N, claim] packing active iff tau>sqrt(rho)+rho/2={thrR2:.4f}:  window active? {tau>thrR2}")
    # Johnson denominator at window, reading R2 with M=N normalized to 1: a=(2tau-rho), w=4 rho, M=1
    a=2*tau-rho; w=4*rho; M=1.0
    denom=a*a-w*M
    print(f"    [R2] descended size a=2tau-rho={a:.4f}, overlap-frac w=4 rho={w:.4f}; "
          f"Johnson denom a^2-w = {denom:.4f}  ({'POSITIVE: bound active' if denom>0 else 'NEGATIVE/0: bound VACUOUS'})")
    # also reading R1 denom: a=tau, w=2 rho, M=1
    a1=tau; w1=2*rho
    denom1=a1*a1-w1*M
    print(f"    [R1] a=tau={a1:.4f}, w=2 rho={w1:.4f}; denom a^2-w = {denom1:.4f}  "
          f"({'POSITIVE' if denom1>0 else 'NEGATIVE/0: VACUOUS'})")
    return dict(rho=rho,tau=tau,sqrt_rho=sqrt_rho,thrR1=thrR1,thrR2=thrR2,
                denomR2=denom,denomR1=denom1,
                window_excluded_R1=not(tau>thrR1), window_excluded_R2=not(tau>thrR2))

if __name__=="__main__":
    print("="*90)
    print("#444 PACKING THRESHOLD DERIVATION (Task 2)")
    print("="*90)
    rows=[analyze(r) for r in (1/8,1/16,1/4,1/2,1/32)]
    print("\n  SUMMARY: is the window tau=2rho EXCLUDED by the packing bound (bound vacuous in window)?")
    for r in rows:
        print(f"    rho={r['rho']:.5f}: window tau={r['tau']:.4f} ; excluded by R1 packing? {r['window_excluded_R1']} ; "
              f"by R2(claim) packing? {r['window_excluded_R2']}")
    print("\n  CONCLUSION CHECK: claim says packing 'reduces to Johnson' i.e. only works for tau>sqrt(rho)+rho/2,")
    print("  and the window tau<sqrt(rho) is INSIDE (below) that threshold => packing gives NO bound in the window.")
