#!/usr/bin/env python3
"""Fiber-Chebyshev refinement: where the (k-1) fiber cap is REAL and where it
is REFUTED.

Claim under test (cross-cone round bonus): per-direction rider counts obey
#{s : fiber >= b} <= (k-1)F/b^2, refining the vote bound F/b when b > k-1.

Mechanism audit (exact):
  * The cap 'each fiber <= k-1' needs the fiber to be the zero set of a NONZERO
    DEG<k POLYNOMIAL, i.e. BOTH components of the ratio map must be codewords.
  * CODEWORD-PAIR CASE (pencil differences, foreign-region votes): rider gamma
    of pencil a votes at i in alignedSet(b) iff r0(i) + gamma*r1(i) = 0 with
    r = (wb - wa) rows, BOTH codewords -> fiber = zeros of a codeword <= k-1
    (except at most ONE proportionality scalar).  CAP REAL.
  * U-RELATIVE CASE (the derecursion stall ledger): rho = (u1 - w)/D with
    NEITHER component a codeword -> a single fiber can be as large as the pool
    (adversarial u1 = w + s0*D on a huge set).  CAP REFUTED: the stall boundary
    F0 does NOT move by this mechanism.

Sections: (A) codeword-pair fibers at mu_256 (exact sweep, expect <= k-1 with
equality achievable); (B) u-relative counterexample (fiber >> k-1); (C) the
crossover and swarm-floor arithmetic incl. the no-fully-foreign-rider constant.
"""

import numpy as np

q, Nn, T, k = 1031, 256, 142, 64
dom = list(range(Nn))
V = np.array([[pow(x, j, q) for j in range(k)] for x in dom], dtype=np.int64)
rng = np.random.default_rng(99)


def modinv(a):
    return pow(int(a) % q, q - 2, q)


print("=" * 78)
print("A. Codeword-pair fibers (pencil-difference ratio maps) at mu_256: <= k-1")
print("=" * 78)
worst = 0
for trial in range(200):
    r0 = (V @ rng.integers(0, q, k)) % q
    r1 = (V @ rng.integers(0, q, k)) % q
    fibers = {}
    for i in range(Nn):
        if r1[i] != 0:
            g = (-int(r0[i]) * modinv(r1[i])) % q
            fibers[g] = fibers.get(g, 0) + 1
        elif r0[i] == 0:
            pass  # both zero: i is a common root, belongs to every gamma's fiber
    mx = max(fibers.values()) if fibers else 0
    worst = max(worst, mx)
print(f"  200 random codeword pairs: max fiber = {worst} <= k-1 = {k-1}:"
      f" {worst <= k - 1}")
# adversarial: r0 = -5 * r1 * (near-proportional but distinct) is excluded;
# make a fiber of size exactly k-1: r0 + 5*r1 = z_{k-1 roots}:
roots = list(range(k - 1))
zpoly_eval = np.ones(Nn, dtype=np.int64)
for r in roots:
    zpoly_eval = zpoly_eval * (np.arange(Nn) - r) % q
r1 = (V @ rng.integers(0, q, k)) % q
r0 = (zpoly_eval - 5 * r1) % q  # r0 + 5 r1 = z (deg k-1 <= k-1: codeword) ✓
fib5 = sum(1 for i in range(Nn)
           if (r0[i] + 5 * r1[i]) % q == 0)
print(f"  adversarial pair: fiber at gamma=5 has size {fib5} = k-1 = {k-1}"
      f" (cap TIGHT)")

print("\n" + "=" * 78)
print("B. U-relative ratio maps (the stall ledger's rho = (u1-w)/D): cap REFUTED")
print("=" * 78)
# D arbitrary word (nonzero on pool), w codeword, u1 := w + s0*D on a large set S
w = (V @ rng.integers(0, q, k)) % q
D = rng.integers(1, q, Nn).astype(np.int64)   # pool everywhere
s0 = 7
S = list(range(200))                          # 200 >> k-1 = 63 coordinates
u1 = (w + 3) % q                              # generic off S
u1 = np.array(u1)
for i in S:
    u1[i] = (w[i] + s0 * D[i]) % q
fib = {}
for i in range(Nn):
    s = (int(u1[i] - w[i]) * modinv(D[i])) % q
    fib[s] = fib.get(s, 0) + 1
print(f"  adversarial u1: fiber of rho=(u1-w)/D at s0={s0} has size {fib[s0]}"
      f" >> k-1 = {k-1}  -> the (k-1) cap FAILS u-relatively;")
print("  the derecursion boundary F0 does NOT move by this mechanism (the")
print("  stall ledger's ratio components are not codewords).")

print("\n" + "=" * 78)
print("C. Crossover + swarm-floor arithmetic (prize constants, exact)")
print("=" * 78)
N, Tp, kp = 2**30, 592794966, 2**28
print(f"  refinement beats the vote bound iff b = T - A > k-1, i.e."
      f" A < T-k+1 = {Tp - kp + 1}")
print(f"  pair-pencil floor A = 2T-N = {2*Tp - N} < {Tp - kp + 1}:"
      f" {2*Tp - N < Tp - kp + 1} (the ENTIRE floor regime is refined)")
lhs = (kp - 1) * (Tp - 1)
rhs = (N - Tp) * (N - Tp)
print(f"  no-fully-foreign-rider: (k-1)(T-1) = {lhs} < (N-T)^2 = {rhs}:"
      f" {lhs < rhs}")
print("  -> no rider can collect ALL its N-T-scale votes inside one foreign")
print("     aligned region (second moment forbids it).")
b = N - Tp
print(f"  refinement factor at the floor: b/(k-1) = {b/(kp-1):.3f}")
