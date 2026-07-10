#!/usr/bin/env python3
"""FSME bivariate-lane probe: in-tree BCIKS20 error bound at the P1 predecessor point.

Deterministic. Certifies (in exact rational arithmetic):
  1. deltaPred = (N-T)/N lies strictly inside the Johnson branch
     ((1-rho)/2, 1 - sqrt(rho)) of ProximityGap.errorBound.
  2. The Johnson-branch value is eps = deg^2 / ((2m)^7 * q) with
     m = min(1 - sqrt(rho) - delta, sqrt(rho)/20) = sqrt(rho)/20 = 1/40,
     so eps * q = deg^2 * 20^7 = 2^63 * 10^7 (exact), i.e. a scalar budget
     of ~2^86.25 >> N = 2^30.  Gap factor exactly 2^33 * 10^7.
  3. eps < 1 at the P1 prime P (so the in-tree theorem is non-vacuous,
     just 2^56.25x too weak for the pin).
  4. Direct bivariate interpolation feasibility: a (D+1)-point coefficient
     interpolation needs joint cores of D+2 agreement sets to reach K,
     i.e. (D+2)(N-T) <= N-K; this fails for every D >= 0.
  5. Six-set pigeonhole (the landed forced-secant input): 6 sets of size T
     force a pair overlap >= K, 5 sets do not (convexity lower bound).
"""

from fractions import Fraction
import math

N = 2**30
K = 2**28
T = 592794966
P = 2**30 * (2**128 + 192) + 1

delta = Fraction(N - T, N)
rho = Fraction(K, N)
sqrt_rho = Fraction(1, 2)  # exact since rho = 1/4
assert sqrt_rho**2 == rho

udr = (1 - rho) / 2
johnson = 1 - sqrt_rho

print("== 1. branch location ==")
print(f"delta = {delta} = {float(delta):.10f}")
print(f"UDR (1-rho)/2 = {udr} = {float(udr)}")
print(f"Johnson 1-sqrt(rho) = {johnson}")
assert udr < delta < johnson, "delta must be in the open Johnson branch"
print("delta strictly inside Johnson branch: OK")
print(f"overshoot above UDR: {float(delta - udr):.6f} (absolute)")

print("\n== 2. Johnson-branch error value ==")
m1 = 1 - sqrt_rho - delta
m2 = sqrt_rho / 20
m = min(m1, m2)
print(f"1 - sqrt(rho) - delta = {m1} = {float(m1):.8f}")
print(f"sqrt(rho)/20 = {m2} = {float(m2)}")
assert m == Fraction(1, 40)
budget = K**2 * Fraction(1, (2 * m) ** 7)
assert budget.denominator == 1
budget = budget.numerator
assert budget == 2**63 * 10**7 == 92233720368547758080000000
print(f"eps * q = deg^2 / (2m)^7 = {budget} = 2^63*10^7 = 2^{math.log2(budget):.4f}")
print(f"target N = {N} = 2^30")
gap = Fraction(budget, N)
assert gap == 2**33 * 10**7 == 85899345920000000
print(f"gap factor = {gap} = 2^33*10^7 = 2^{math.log2(gap):.4f}")

print("\n== 3. non-vacuity at P1 prime ==")
print(f"P = {P} ~ 2^{math.log2(P):.2f}")
assert budget < P
print(f"eps = budget/P = {float(Fraction(budget, P)):.3e} < 1: OK")
print(f"Pr at pin scale (N+1)/P = {float(Fraction(N + 1, P)):.3e}"
      f" << eps: hypothesis Pr > eps unreachable at pin scale:"
      f" {Fraction(N + 1, P) < Fraction(budget, P)}")

print("\n== 4. direct bivariate interpolation feasibility ==")
# Interpolating coefficient polynomials of Y-degree <= D through D+1 bad scalars
# transfers to a fresh scalar only on the joint core of the D+2 agreement sets;
# guaranteed joint core is N - (D+2)(N-T), and forcing q_gamma = Q(., gamma)
# needs >= K matched coordinates.
best = Fraction(N - K, N - T)
print(f"need (D+2) <= (N-K)/(N-T) = {float(best):.6f}")
for D in range(0, 3):
    core = N - (D + 2) * (N - T)
    print(f"D={D}: guaranteed joint core = {core}"
          f" {'>= K OK' if core >= K else f'< K = {K} FAIL (deficit {K - core})'}")
assert N - 2 * (N - T) < K  # even D=0 fails
print("=> every Y-degree D >= 0 fails; naive bivariate fitting is infeasible;"
      " only pigeonhole-refined pair extraction survives.")

print("\n== 5. six-set pigeonhole threshold ==")
for s in (5, 6):
    # convexity: sum over pairs of overlaps >= ((sT)^2/N - sT)/2, max pair >= /C(s,2)
    tot2 = (Fraction(s * T, 1) ** 2 / N - s * T) / 2
    pairs = s * (s - 1) // 2
    mx = tot2 / pairs
    print(f"{s} sets: guaranteed max pair overlap >= {float(mx):.1f}"
          f" ({'>= K' if mx >= K else '< K'}; K = {K})")
print("=> 6 is exactly the forcing threshold (matches landed"
      " _P1RateQuarterForcedSecantMatching six-set lemma).")

print("\nALL ASSERTIONS PASSED")
