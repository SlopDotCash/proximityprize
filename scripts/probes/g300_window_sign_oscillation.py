#!/usr/bin/env python3
"""
G300 exact probe: the in-window CORE covariance sign genuinely oscillates.

Companion to G299 (`_G299PrizeDepthInWindow.lean`), which proved the prize depth r* ~ 89 and its
palindromic reflection n+1-r* both lie INSIDE the low-rank window [2, n-1] at production
(q = 2^158, n = 2^30). If the covariance A_r were sign-definite / rank-monotone / a single sign
band on the window, that in-window placement would immediately sign the CORE covariance at the
prize depth from cheap boundary data. This probe shows the covariance sign genuinely OSCILLATES
inside the window, killing every such shortcut.

Model (exact, integer, matches G295/G298):
  G <= F_p^*  the order-n multiplicative subgroup (n even, sponsor 2-power regime),
  W_G(x) = #{(y,z) in G^2 : 2y - z = x},
  dp_r(x) = number of r-subsets of G summing to x   (dp_0 = 1_{0}),
  R_r = dp_r * dp_{r-1}   (cyclic convolution mod p),
  A_r = p * sum_x W_G(x) R_r(x) - (sum W_G)(sum R_r).

Checks (all pure integer, hard SystemExit(1) on any violation):
  1. G295 palindrome A_r = A_{n+1-r} holds on every sponsor cell (n in {8,16,32}, p = 1 mod n).
  2. The Lean (113,8) witness reproduces EXACTLY:
       A_r (r=1..7) = [392, 128, -7240, -13128, -13128, -7240, 128],
       and the load-bearing values A_2 = 128 > 0, A_4 = -13128 < 0, A_7 = 128 > 0
       (an interior sign change: + at r=2, - at r=4, + at r=7, all in window [2,7]).
       Also the exact marginals used by the Lean proof: sum W = 64, sum R_2 = 224,
       sum R_4 = 3920, dot(W,R_2) = 128, dot(W,R_4) = 2104.
  3. Interior sign changes are NOT a small-cell artifact: (257,32) has the period-4 profile with
     >= 8 interior sign changes strictly inside [5, n-5]; assert at least 8.
  4. Sign-definiteness FAILS in general: at least one sponsor cell has a strictly interior sign
     change (A positive at some rank, negative at another, both in [2, n-1]).
"""
import sys


def subgroup(p, n):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        o = 1
        xx = cand % p
        while xx != 1:
            xx = (xx * cand) % p
            o += 1
            if o > p:
                break
        if o == p - 1:
            g = cand
            break
    assert g is not None, (p, n)
    h = pow(g, (p - 1) // n, p)
    G = []
    v = 1
    for _ in range(n):
        G.append(v)
        v = (v * h) % p
    assert len(set(G)) == n
    return sorted(set(G))


def W_G(G, p):
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    return W


def dp_seq(G, p, maxr):
    dp = [[0] * p for _ in range(maxr + 1)]
    dp[0][0] = 1
    for g in G:
        for k in range(min(maxr, len(G)), 0, -1):
            row = dp[k]
            prev = dp[k - 1]
            for x in range(p):
                if prev[x]:
                    row[(x + g) % p] += prev[x]
    return dp


def convolve(a, b, p):
    r = [0] * p
    for i in range(p):
        if a[i]:
            ai = a[i]
            for j in range(p):
                if b[j]:
                    r[(i + j) % p] += ai * b[j]
    return r


def A_seq(p, n):
    G = subgroup(p, n)
    W = W_G(G, p)
    dp = dp_seq(G, p, n - 1)
    sW = sum(W)
    out = []
    rows = []
    for r in range(1, n):
        Rr = convolve(dp[r], dp[r - 1], p)
        rows.append(Rr)
        out.append(p * sum(W[x] * Rr[x] for x in range(p)) - sW * sum(Rr))
    return G, W, rows, out


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def sponsors(nvals, pmax):
    out = []
    for n in nvals:
        for p in range(n + 1, pmax):
            if (p - 1) % n == 0 and p > 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
                out.append((p, n))
    return out


# --- Check 1: G295 palindrome on every sponsor cell ---
for (p, n) in sponsors([8, 16, 32], 400):
    _, _, _, A = A_seq(p, n)  # A[r-1] = A_r, r=1..n-1
    for r in range(2, n):
        if A[r - 1] != A[(n + 1 - r) - 1]:
            fail(f"palindrome A_r=A_(n+1-r) broken at p={p} n={n} r={r}")
print("check 1 OK: palindrome A_r = A_{n+1-r} on all sponsor cells n in {8,16,32}, p<400")

# --- Check 2: exact (113,8) Lean witness ---
G, W, rows, A = A_seq(113, 8)
expect = [392, 128, -7240, -13128, -13128, -7240, 128]
if A != expect:
    fail(f"(113,8) A-sequence mismatch: got {A} expected {expect}")
if not (A[1] > 0 and A[3] < 0 and A[6] > 0):
    fail(f"(113,8) interior sign change absent: A_2={A[1]} A_4={A[3]} A_7={A[6]}")
# exact marginals used by the Lean proof
sW = sum(W)
R2, R4 = rows[1], rows[3]
sR2, sR4 = sum(R2), sum(R4)
dot2 = sum(W[x] * R2[x] for x in range(113))
dot4 = sum(W[x] * R4[x] for x in range(113))
if (sW, sR2, sR4, dot2, dot4) != (64, 224, 3920, 128, 2104):
    fail(f"(113,8) marginals mismatch: sumW={sW} sumR2={sR2} sumR4={sR4} dot2={dot2} dot4={dot4}")
# confirm the centered form reproduces from the marginals
if 113 * dot2 - sW * sR2 != 128:
    fail("A_2 marginal reconstruction != 128")
if 113 * dot4 - sW * sR4 != -13128:
    fail("A_4 marginal reconstruction != -13128")
# reflection row equality (R_7 residue table == R_2)
R7 = rows[6]
if R7 != R2:
    fail("(113,8) reflection row R_7 != R_2 as tabulation")
print("check 2 OK: (113,8) witness exact: A=[392,128,-7240,-13128,-13128,-7240,128], "
      "marginals (64,224,3920,128,2104), R_7 table == R_2 table")

# --- Check 3: deep oscillation on (257,32), >= 8 strictly-interior sign changes ---
_, _, _, A = A_seq(257, 32)
signs = [1 if a > 0 else (-1 if a < 0 else 0) for a in A]  # r=1..31
interior = [r for r in range(5, 31 - 4) if signs[r - 1] * signs[r] < 0]
if len(interior) < 8:
    fail(f"(257,32) too few interior sign changes: {len(interior)} at {interior}")
print(f"check 3 OK: (257,32) has {len(interior)} strictly-interior sign changes at r={interior}")

# --- Check 4: sign-definiteness fails on some cell (interior positive AND negative) ---
found = False
for (p, n) in sponsors([8, 16, 32], 400):
    _, _, _, A = A_seq(p, n)
    win = A[1:n - 1]  # A_2 .. A_{n-1}
    if any(a > 0 for a in win) and any(a < 0 for a in win):
        found = True
        break
if not found:
    fail("no sponsor cell exhibits a mixed-sign window (unexpected)")
print(f"check 4 OK: window sign is not definite (mixed-sign cell exists, e.g. p={p} n={n})")

print("ALL G300 CHECKS PASS")
