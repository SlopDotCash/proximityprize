#!/usr/bin/env python3
"""
#466 CORE probe — DC-subtracted Stieltjes step-ratio antitonicity.

Companion to `Frontier/_DCStieltjesRatioAntitoneEquivalence.lean`.

Object: A_r := sum_{b!=0} |eta_b|^{2r} = q*E_r(mu_n) - n^{2r}   (DCSubtractedMoment.sum_nonzero_moment),
E_r = #{(x_1..x_r,y_1..y_r) in mu_n^{2r} : sum x = sum y mod p}, computed exactly by integer modular
self-convolution of the subgroup indicator (rep_r), E_r = sum_c rep_r(c)^2.

A_r is a genuine positive (Stieltjes) moment sequence: A_r = sum_{b!=0} lambda_b^r, lambda_b=|eta_b|^2>=0.
Hence rho_r := A_{r+1}/A_r is monotone NON-decreasing (log-convexity, powerSum_ratio_monotone).

We test the Gaussian-normalized ratio R~_r := rho_r / ((2r+1) n) for ANTITONICITY (R~_{r+1} <= R~_r),
equivalently the per-step growth cap  g_r := rho_{r+1}/rho_r <= (2r+3)/(2r+1).

FINDINGS (this probe, exact integer arithmetic):
 - rho_r monotone-UP at EVERY tested prime (Stieltjes log-convexity — the free lower half of the sandwich).
 - R~_r ANTITONE at {F4/gen n16; p=786433 (the K-bad prime where the RAW step-ratio REVERSES); generic n32}.
 - R~_r REVERSES (cap violated) at {p=1391393, 2089889, 4102753 (n32, structured/K-bad)}, with the
   exact caps g_2 in {1.4063, 1.4147, 1.4077} > 7/5 — the abstract `stieltjes_can_violate_cap` witness
   made arithmetic. Antitone failure tracks the LARGEST wall constant C = M/sqrt(2 n log p) (~1.39-1.40
   at the worst violators): DC-subtracted antitonicity is M-EQUIVALENT, not free.
"""
import math
import numpy as np
from sympy import factorint

def gen(p):
    fac = factorint(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no generator")

def subgroup(p, n):
    g = gen(p); h = pow(g, (p - 1) // n, p)
    S = []; x = 1
    for _ in range(n):
        S.append(x); x = x * h % p
    assert len(set(S)) == n
    return S

def dfac(k):
    r, i = 1, 2 * k - 1
    while i > 0:
        r *= i; i -= 2
    return r

def data(p, n, rmax):
    ind = np.zeros(p)
    for s in subgroup(p, n):
        ind[s] = 1.0
    F = np.fft.rfft(ind)
    FT = np.fft.fft(ind); lam = np.abs(FT) ** 2; lam[0] = 0.0
    M2 = float(np.max(lam))
    E = {k: int(round(float(np.sum(np.rint(np.fft.irfft(F ** k, n=p)) ** 2))))
         for k in range(1, rmax + 2)}
    A = {k: p * E[k] - n ** (2 * k) for k in E}
    return A, M2

def analyze(p, n, rmax, label):
    A, M2 = data(p, n, rmax)
    L = math.log(p / n); C = math.sqrt(M2 / (n * L)) if M2 > 0 else float('nan')
    rho = {k: A[k + 1] / A[k] for k in range(1, rmax + 1)}
    Rt = {k: rho[k] / ((2 * k + 1) * n) for k in rho}
    rho_up = all(rho[k + 1] >= rho[k] - 1e-9 for k in range(1, rmax))
    caps = []
    anti = True
    for k in range(1, rmax):
        g = rho[k + 1] / rho[k]; cap = (2 * k + 3) / (2 * k + 1)
        if g > cap + 1e-12:
            anti = False; caps.append((k, round(g, 4), round(cap, 4)))
    print(f"{label:<14} p={p:>10} n={n:>3} b~{math.log(p)/math.log(n):.2f} "
          f"C={C:.4f}  rho-UP:{rho_up}  R~-ANTITONE:{anti}  cap-viol:{caps}")
    return rho_up, anti, C

if __name__ == "__main__":
    print("# DC-subtracted Stieltjes step-ratio: rho monotone-UP (free), R~ antitone (M-equivalent)")
    tests = [
        (65537, 16, "F4-n16"), (65617, 16, "gen-n16"), (114689, 16, "n16-b4.2"),
        (786433, 32, "KBAD-n32"), (1048609, 32, "gen-n32"),
        (1391393, 32, "KBAD2-n32"), (2089889, 32, "KBAD3-n32"), (4102753, 32, "KBAD4-n32"),
    ]
    allup = True; res = {}
    for p, n, lab in tests:
        up, anti, C = analyze(p, n, 8, lab)
        allup = allup and up; res[lab] = anti
    print(f"\n# rho monotone-UP at ALL primes (Stieltjes, expected True): {allup}")
    print(f"# R~ antitone per prime: {res}")
    print("# => antitonicity is NOT structurally forced; it fails at the largest-C structured primes")
    print("#    (KBAD2/3/4), i.e. it is equivalent-in-difficulty to the M-bound. QED (empirical).")
