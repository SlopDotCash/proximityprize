#!/usr/bin/env python3
"""_FSMA_SecondMoment probe: exact Plotkin caps on near-saturated cores at P1,
and second-moment pair-mass feasibility analysis.

P1 parameters: N = 2^30, K = 2^28, T = 592794966.
Cores of distinct secant lines are subsets of [N] with pairwise intersection
<= K-1 (root bound rigidity).  constantWeight_plotkin (after shrinking every
core to exactly w = z0 elements; intersections only shrink):

   m * (w^2 - N*lam) <= N * (w - lam)   whenever w^2 > N*lam,

so m <= N*(w - lam) / (w^2 - N*lam).

Companion Lean file:
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FSMA_SecondMomentPairPartition.lean
"""
from fractions import Fraction
import math

N = 2**30
K = 2**28
T = 592794966
lam = K - 1
NKm1 = N * lam

print("N =", N, " K =", K, " T =", T, " lam = K-1 =", lam)
print("N*lam =", NKm1)
print("2T - N =", 2*T - N, " (<= K-1?", 2*T - N <= lam, ")")
print("T-2 =", T-2, "  max line size Lmax = N-T+1 =", N-T+1)
print()

def cap(z0):
    """Plotkin cap on # sets of size >= z0 pairwise overlapping <= lam."""
    den = z0*z0 - NKm1
    return Fraction(N*(z0 - lam), den) if den > 0 else None

zc = math.isqrt(NKm1) + 1
print("Plotkin applies for z0 >=", zc, "(z0^2 > N*(K-1))")
for z0 in [zc, 2**29, 550000000, 570000000, 587673607, T-2, T, 599424501,
           618146628, 652432610, 733379304]:
    c = cap(z0)
    print(f"z0 = {z0:>11}: cap = {float(c):18.6f}  floor = {c.numerator//c.denominator}")
print()

# smallest z0 with cap < bound (bound = 1 unreachable: cap -> 1+ as z0 -> N)
for bound in [10, 9, 8, 7, 6, 5, 4, 3, 2]:
    lo, hi = zc, N
    while lo < hi:
        mid = (lo+hi)//2
        if N*(mid-lam) < bound*(mid*mid - NKm1):
            hi = mid
        else:
            lo = mid+1
    z0 = lo
    assert cap(z0) < bound and (cap(z0-1) is None or cap(z0-1) >= bound)
    rel = "<= T-2" if z0 <= T-2 else " > T-2"
    print(f"smallest z0 with cap < {bound:>2}: z0 = {z0} ({rel}, T-2-z0 = {T-2-z0})")
print()

# Exact Lean-instance inequalities: m sets of size >= t impossible iff
# N*(t-lam) < m*(t^2 - N*lam); sharpness = flip at t-1.
print("Lean norm_num instances (impossible=True at t, False at t-1):")
for (m, t) in [(6, 587673607), (6, T-2), (5, 599424501), (4, 618146628),
               (3, 652432610), (2, 733379304)]:
    ok = N*(t-lam) < m*(t*t - NKm1)
    sharp = not (N*(t-1-lam) < m*((t-1)*(t-1) - NKm1))
    print(f"  m={m} t={t}: impossible={ok}, sharp(t-1 satisfiable)={sharp}")
print()

# Fresh-fibre packing: L*(T-z) + z <= N (for z < T) forces z >= (L*T-N)/(L-1).
def zmin_f(L):
    return -((-(L*T - N))//(L-1))

print("core forcing zmin(L) = ceil((L*T-N)/(L-1)):")
for L in [2, 3, 10, 94, 95, 96, 100, 1000, 240473430, 240473431, N-T+1]:
    z = zmin_f(L)
    c = cap(z)
    cstr = "None" if c is None else f"{float(c):.6f}"
    print(f"  L = {L:>10}: zmin = {z}  cap(zmin) = {cstr}")
print("L = 95 forces z >= 587678511 >= fivePencilCoreFloor = 587673607:",
      zmin_f(95) >= 587673607, " (L = 94: zmin =", zmin_f(94), ")")
print("L = 240473431 forces z >=", zmin_f(240473431), "= T-1:",
      zmin_f(240473431) == T - 1)
print()

# Pair-mass window certificates.
Lmax = N - T + 1
need = (N+1)*N
print("(N+1)*N              =", need)
print("5*Lmax*(Lmax-1)      =", 5*Lmax*(Lmax-1), " > need:", 5*Lmax*(Lmax-1) > need,
      " ratio:", 5*Lmax*(Lmax-1)/need)
print("4*Lmax*(Lmax-1)      =", 4*Lmax*(Lmax-1), " < need:", 4*Lmax*(Lmax-1) < need)
print()

# Knapsack: max pair mass on lines with >= 10 points subject to the FULL
# Plotkin ladder (rank j line must satisfy cap(zmin(L_j)) >= j).
def cap_floor(z0):
    den = z0*z0 - NKm1
    return (N*(z0-lam))//den if den > 0 else None

def max_L_at_rank(j):
    lo, hi, best = 10, Lmax, 9
    while lo <= hi:
        mid = (lo+hi)//2
        c = cap_floor(zmin_f(mid))
        if c is None or c >= j:
            best = mid
            lo = mid+1
        else:
            hi = mid-1
    return best

tot = 0
ranks = []
for j in range(1, 200):
    Lj = max_L_at_rank(j)
    if Lj <= 9:
        break
    ranks.append(Lj)
    tot += Lj*(Lj-1)
print("ladder-constrained sorted max line sizes (first 12 ranks):", ranks[:12])
print("number of ranks with >= 10 points allowed:", len(ranks))
print("max pair mass on lines with >= 10 points  :", tot)
print("required pair mass (N+1)*N                :", need)
print("big-line channel alone sufficient?", tot >= need, " ratio:", tot/need)
print()
print("BARRIER NOTE: lines with <= 9 points can carry unbounded pair mass")
print("(the identity is self-satisfiable by 2-point lines), so pair-mass")
print("counting alone can never contradict |G| > N; the ladder only pins the")
print("geometry of the >= 10-point lines.")

# High-core collapse vacuity at P1: 3T + 2z > 2N + 4(K-1) needs z >= ...
zz = 2*N + 4*(K-1) - 3*T
print()
print("high-core collapse needs z >=", zz//2 + 1, "> T-2 =", T-2,
      "-> vacuous at P1:", zz//2 + 1 > T-2)
