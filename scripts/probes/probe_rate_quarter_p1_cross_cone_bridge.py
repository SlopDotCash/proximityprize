#!/usr/bin/env python3
"""Cross-cone bridge probe: the P1 swarm's second-moment layer and the B-side
lag machinery are instances of ONE generic identity family; the OPEN layers are
provably different regimes (completeness-ratio calibration).

(1) P1 swarm side, exact shape: swarm riders on a direction w against the stack
    (u1, -D) are fibers of the ratio map rho_w = (u1 - w)/D — the swarm count is
    fiber statistics of rational maps on the (subgroup-structured) domain.  The
    fiber-count function h(s) = #{x in X : rho(x) = s} has DFT
    h^(a) = Sum_{x in X} e(a*rho(x))  — the INCOMPLETE exponential sum — and:
      * Parseval:      Sum_a |h^(a)|^2 = M * Sum_s h(s)^2   (fiber energy)
      * lag Parseval:  Sum_a |h^(a)|^4 = M * Sum_t |autocorr h (t)|^2
    — the SAME identities the B-side uses for the Jacobi ladder (R309's
    fourthMoment_eq_lag_energy), with f = fiber-count instead of f = ladder.
(2) Verify both identities exactly/numerically at small scale.
(3) Calibrate the NON-bridge at the open layers: the swarm's incomplete sums
    have length N = 2^30 over F_P with N^4 < P < N^6 (theta = log_P N ~ 0.19 <
    1/4 = Burgess): below the Burgess range, only subgroup-specific (BGK)
    methods exist.  The B-side sums are COMPLETE (ratio 1); its open input is
    the r=4 family average (OffZeroQuadLagBound ~ m^{3/2} q^2).  The walls
    differ in completeness ratio and in moment depth.
"""

import cmath
import numpy as np

# ---------------------------------------------------------------------------
print("=" * 78)
print("(2) Bridge identities, exact at small scale (M = 257, X = mu_16-like)")
print("=" * 78)
M = 257
g = 3
w16 = pow(g, (M - 1) // 16, M)
X = sorted({pow(w16, i, M) for i in range(16)})  # mu_16 in F_257
rng = np.random.default_rng(7)
# rho: a rational map deg<k analogue — take rho(x) = (a0 + a1 x + a2 x^2) * inv(x + 5)
a0, a1, a2 = 11, 7, 3


def rho(x):
    num = (a0 + a1 * x + a2 * x * x) % M
    den = (x + 5) % M
    return num * pow(den, M - 2, M) % M


h = [0] * M
for x in X:
    h[rho(x)] += 1
E_fiber = sum(v * v for v in h)
E_pairs = sum(1 for x in X for y in X if rho(x) == rho(y))
print(f"  fiber energy Sum h^2 = {E_fiber} = #pairs(rho x = rho y) = {E_pairs}:"
      f" {E_fiber == E_pairs}")


def e(t):
    return cmath.exp(2j * cmath.pi * t / M)


# DFT of h vs incomplete sums
ok_dft = True
for a in (0, 1, 5, 100):
    lhs = sum(e(a * s) * h[s] for s in range(M))
    rhs = sum(e(a * rho(x)) for x in X)
    ok_dft &= abs(lhs - rhs) < 1e-9
print(f"  hatF(fiberCount) = incomplete exponential sum (spot checks): {ok_dft}")
S2 = sum(abs(sum(e(a * rho(x)) for x in X)) ** 2 for a in range(M))
print(f"  Parseval: Sum_a|S(a)|^2 = {S2:.6f} vs M*E_fiber = {M * E_fiber}:"
      f" {abs(S2 - M * E_fiber) < 1e-6}")
S4 = sum(abs(sum(e(a * rho(x)) for x in X)) ** 4 for a in range(M))
lag = [sum(h[(j + t) % M] * h[j] for j in range(M)) for t in range(M)]
lagE = sum(v * v for v in lag)
print(f"  lag Parseval: Sum_a|S(a)|^4 = {S4:.6f} vs M*Sum_t|autocorr|^2 ="
      f" {M * lagE}: {abs(S4 - M * lagE) < 1e-4}")
print("  -> the P1 swarm second/fourth-moment layer and the B-side Jacobi lag")
print("     machinery are instances of the SAME generic hatF/autocorr identities")
print("     (R309 fourthMoment_eq_lag_energy with f = fiberCount).")

# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("(3) Calibrated NON-bridge at the open layers")
print("=" * 78)
P = 365375409332725729550921208179070755120141565953
N = 2 ** 30
print(f"  P1 swarm incomplete-sum length: N = 2^30 over F_P (P ~ 2^"
      f"{P.bit_length() - 1})")
print(f"  N^4 < P: {N**4 < P}   P < N^6: {P < N**6}"
      f"   theta = log_P N = {30 / (P.bit_length() - 1):.4f} < 1/4 (Burgess)")
print("  -> the swarm's sums are BELOW the Burgess range: no general-modulus")
print("     technique applies; only subgroup-specific (BGK) methods — and the")
print("     needed statement is LIST-level (beyond all fixed moments: the exact")
print("     second moment gives Chebyshev counts ~ P^(k-2), astronomically above")
print("     the needed <= N).")
print("  B-side: J_j are COMPLETE character sums over F_q (ratio 1, each = sqrt q")
print("     by Weil); the open inputs are FAMILY averages at fixed depth:")
print("     OffZeroLagBound ~ sqrt(m)*q (depth 1), OffZeroQuadLagBound ~")
print("     m^(3/2)*q^2 (depth 2, r = 4).")
print("  STRUCTURAL DISTINCTION (exact): completeness ratio 2^-128 vs 1;")
print("     needed depth: list-level vs r = 4.  A formal reduction would have to")
print("     transport bounds across the completeness ratio, which character-sum")
print("     technology does not do.  The bridge that EXISTS is the shared")
print("     second-moment identity layer (formalized); the walls above it are")
print("     DIFFERENT objects.")
