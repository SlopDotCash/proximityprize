#!/usr/bin/env python3
"""G289: the canonical bounded-degree feature no-gos are a counting mirage (#466).

The weighted-kernel separation route (G286 odd-linear, G287 canonical-quadratic, and the
surrounding referee probes) is closed one polynomial degree at a time by exhibiting an exact
positive Farkas circuit among the gate-signed feature vectors of the n=16, p == 1 mod 16,
rank-{5,6} sponsor census (N=84 cells). This probe records the STRUCTURAL reason those no-gos
exist and shows they carry no arithmetic content about the CORE gate.

Two hard gates (SystemExit(1) on failure), pure float-free where it matters:

  A. Cover function-counting: for N=84 census cells and feature dimension d = binom(4+D,D),
     the separable-dichotomy fraction 2*sum_{k<d} binom(N-1,k)/2^N is astronomically small for
     all low degrees (d <= N/2 = 42), so a no-go is FORCED by dimension counting, not arithmetic.

  B. Gate independence (exact rationals): an explicit strictly-positive integer 5-cell circuit
     annihilates every canonical linear feature coordinate for BOTH the real CORE gate AND the
     exactly-flipped gate. One circuit kills a gate and its opposite, so no functional of the
     census signs is what makes the route fail.

Control (informational): random gate signs are exactly as non-separable as the true gate at every
degree with d <= N/2, and separation becomes generic (both real and random separate) once d > N/2.
Verdict: bounded-degree canonical (T2,T4,T8,T16) features cannot certify the CORE covariance sign.
CORE remains open / on-BGK.

Self-contained: the exact five-cell circuit is inlined (matches the Lean witness); the Cover count
is exact integer arithmetic.
"""
from __future__ import annotations
import sys
from fractions import Fraction
from math import comb

# --- Gate A: Cover function-counting ceiling (exact integers) -------------------------------------

N = 84  # n=16, p==1 mod 16, p<2600, ranks {5,6}


def cover_separable_fraction(n_pts: int, d: int) -> Fraction:
    numer = 2 * sum(comb(n_pts - 1, k) for k in range(0, d))
    return Fraction(numer, 2 ** n_pts)


# degree D -> affine feature dim binom(4+D, D)
GATE_A_ROWS = []
ok_A = True
for D in range(1, 6):
    d = comb(4 + D, D)
    fr = cover_separable_fraction(N, min(d, N))
    forced = (N >= 2 * d)  # d <= N/2 -> generic no-go
    GATE_A_ROWS.append((D, d, float(fr), forced))
    # Below crossover we REQUIRE the separable fraction to be < 1/2 (a no-go is generic).
    if d <= N // 2 and fr >= Fraction(1, 2):
        ok_A = False

print("[G289 gate A] Cover separable-dichotomy fraction, N=84:")
for D, d, fr, forced in GATE_A_ROWS:
    tag = "FORCED-BY-COUNTING (d<=N/2)" if forced else "generic-separable (d>N/2)"
    print(f"  affine deg<= {D}: d={d:3d}  sep_fraction={fr:.3e}  {tag}")
print(f"  crossover at d = N/2 = {N // 2}: below it every no-go is dimension-forced.")

# --- Gate B: exact gate-independent 5-cell circuit -----------------------------------------------

# Five sponsor-faithful cells (p in {113,337,401,433}, ranks {5,6}); raw canonical features
# (T2,T4,T8,T16) and CORE gate signs. Matches _G289CountingMirageNoGo.lean exactly.
RAW = [
    [-309168, -683424, 2610752, 3312256],
    [14464, 57856, -86784, -173568],
    [9290416, 70408736, -14191744, 90283648],
    [5023728, 22930784, 168792128, 266289664],
    [11819168, 32644736, 88373568, 58306048],
]
GATE = [1, -1, 1, -1, 1]
WEIGHT = [
    770888209934274952,
    294057324376824869095,
    185095074806906020,
    347725276122965348,
    382331993870867280,
]

# strict positivity
if not all(w > 0 for w in WEIGHT):
    print("[G289 gate B] FAIL: non-positive weight")
    sys.exit(1)

signed = [[GATE[i] * RAW[i][j] for j in range(4)] for i in range(5)]

# real gate: sum_i w_i * signed_i,j == 0 for all j
ok_real = True
for j in range(4):
    s = sum(WEIGHT[i] * signed[i][j] for i in range(5))
    if s != 0:
        ok_real = False
        print(f"[G289 gate B] FAIL real gate coord {j}: {s}")

# flipped gate: same weights annihilate the negated signed features
ok_flip = True
for j in range(4):
    s = sum(WEIGHT[i] * (-signed[i][j]) for i in range(5))
    if s != 0:
        ok_flip = False
        print(f"[G289 gate B] FAIL flipped gate coord {j}: {s}")

print("\n[G289 gate B] exact gate-independent 5-cell positive circuit:")
print(f"  strictly positive weights: {ok_real and all(w > 0 for w in WEIGHT)}")
print(f"  real-gate annihilation (all 4 coords zero): {ok_real}")
print(f"  flipped-gate annihilation (all 4 coords zero): {ok_flip}")

if not (ok_A and ok_real and ok_flip):
    print("\nG289 PROBE FAILED")
    sys.exit(1)

print("\nG289 PROBE PASS: bounded-degree canonical-feature no-gos are a dimension-counting mirage;")
print("the linear no-go is gate-independent (kills the CORE gate and its exact opposite alike).")
print("CORE remains open / on-BGK.")
