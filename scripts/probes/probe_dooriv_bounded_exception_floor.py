#!/usr/bin/env python3
"""
Probe the BOUNDED-EXCEPTION sharpening of the deficit-budget converse before formalizing.

Claim: split levels 0..a-1 into good set G (delta_k <= eps, eps < (log2)/2) and
exceptional set E (size e, delta_k <= 1 there, the deep spikes). Then
  S = sum delta_k <= eps*(a-e) + 1*e = eps*a + (1-eps)*e.
The budget bound is 2^a * exp(-S) * M0. We want it >= (sqrt2)^a * M0 = 2^(a/2)*M0,
i.e. exp(-S) >= 2^(-a/2), i.e. S <= (a/2)*log2.
Sufficient: eps*a + (1-eps)*e <= (a/2)*log2
  <=> (1-eps)*e <= ((log2)/2 - eps)*a
  <=> e <= ((log2)/2 - eps)/(1-eps) * a.
So if the exceptional count e is below a positive-density fraction
  rho_eps = ((log2)/2 - eps)/(1-eps)  (>0 since eps < (log2)/2),
the budget STILL stays above sqrt-scale. In particular any SUBLINEAR e=o(a) eventually qualifies.
Verify the algebra + that the bound holds across random configs.
"""
import math, random

L2 = math.log(2)
THRESH = L2/2

def rho_eps(eps):
    return (THRESH - eps)/(1 - eps)

print(f"(log2)/2 = {THRESH:.6f}")
for eps in [0.0, 0.1, 0.2, 0.3, 0.34]:
    print(f"eps={eps:.2f}  density floor rho_eps = {rho_eps(eps):.4f}  (e <= rho_eps*a allowed)")

print("\nrandom verification: budget >= sqrt-scale when e <= rho_eps*a")
random.seed(1)
fails = 0
for trial in range(200000):
    a = random.randint(2, 80)
    eps = random.uniform(0.0, THRESH - 1e-6)
    re = rho_eps(eps)
    e = random.randint(0, max(0, int(re*a)))  # exceptional count within density floor
    # build deltas: e of them <= 1 (set near worst =1), rest <= eps
    deltas = [1.0]*e + [random.uniform(0, eps) for _ in range(a-e)]
    if len(deltas) > a:
        deltas = deltas[:a]
    while len(deltas) < a:
        deltas.append(random.uniform(0, eps))
    S = sum(deltas)
    budget = (2**a) * math.exp(-S)        # / M0
    sqrtscale = math.sqrt(2)**a
    if budget < sqrtscale - 1e-9*sqrtscale:
        fails += 1
        if fails <= 5:
            print(f"  FAIL a={a} eps={eps:.3f} e={e} S={S:.3f} budget<scale")
print(f"fails = {fails} / 200000")

# tight algebra check: S <= eps*a + (1-eps)*e and the sufficient condition
print("\nworst-case S = eps*a + (1-eps)*e (all exceptions =1, all good =eps):")
ok = True
for _ in range(100000):
    a = random.randint(2,80)
    eps = random.uniform(0, THRESH-1e-6)
    re = rho_eps(eps)
    e = random.randint(0, int(re*a)) if int(re*a)>0 else 0
    Sworst = eps*a + (1-eps)*e
    if Sworst > (a/2)*L2 + 1e-9:
        ok = False
        print(f"  ALGEBRA FAIL a={a} eps={eps:.3f} e={e} Sworst={Sworst:.3f} > {(a/2)*L2:.3f}")
        break
print("worst-case algebra holds:", ok)
