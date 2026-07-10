#!/usr/bin/env python3
"""r347 probe: Stickelberger carry vectors - identities, telescoping, rank certificates.

Route 'kummer-hecke-alignment' (#466, session 2026-07-09, companion to r341).
The Rank Lemma core: v_k(t) = <t/m> + <kt/m> - <(k+1)t/m> in {0,1} is the carry
indicator of (t%m) + (k*t%m); the signed vectors w_k = 2*v_k - 1 on the units
t = 1..m-1, k = 1..(m-1)/2, are Q-linearly independent for m an odd prime
(pen-and-paper via Stickelberger telescoping + B_{1,psi} != 0; machine-checked
here per-m), and DEGENERATE for composite m (m=8: w_3 = w_1 exactly, the
finite-order Hecke relation behind the observed beta_3 - beta_1 in {0,pi} atom).

All arithmetic exact (int / Fraction). Exits nonzero on any mismatch.
Outputs the exact matrices + nonsingular minors used by the Lean certificates in
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R347StickelbergerRankCertificates.lean.
"""
from fractions import Fraction
from itertools import combinations
import sys

def md(x, m):
    """Lean Nat convention: x % 0 = x."""
    return x if m == 0 else x % m

def carry(m, k, t):
    """stickCarry m k t: 0 if (t%m) + (k*t%m) < m else 1 (Lean-mirror, incl. m=0)."""
    return 0 if md(t, m) + md(k * t, m) < m else 1

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", msg)

# ---------------------------------------------------------------- 1. identity
# m * v_k(t) = (t%m) + (k*t%m) - ((k+1)*t%m)   for ALL m,k,t (incl. m=0)
for m in range(0, 41):
    B = 3 * max(m, 1) + 2
    for k in range(0, B):
        for t in range(0, B):
            lhs = m * carry(m, k, t)
            rhs = md(t, m) + md(k * t, m) - md((k + 1) * t, m)
            check(lhs == rhs, f"identity m={m} k={k} t={t}: {lhs} != {rhs}")
print("[1] carry identity OK for all m<=40, k,t<=3m+1 (incl. m=0)")

# ------------------------------------------------------------- 2. telescoping
# m * sum_{k=1}^{a} v_k(t) = (a+1)*(t%m) - ((a+1)*t%m)
for m in range(0, 31):
    for t in range(0, 2 * max(m, 1) + 2):
        for a in range(0, 2 * max(m, 1) + 2):
            lhs = m * sum(carry(m, k, t) for k in range(1, a + 1))
            rhs = (a + 1) * md(t, m) - md((a + 1) * t, m)
            check(lhs == rhs, f"telescope m={m} t={t} a={a}: {lhs} != {rhs}")
print("[2] telescoping OK for all m<=30, t,a<=2m+1 (incl. m=0)")

# --------------------------------------------------- 3. rank certificates (Q)
def signed_matrix(m, units=None):
    """rows k=1..K (K=(m-1)/2 for odd prime; pass K explicitly via rows), cols=units."""
    if units is None:
        units = [t for t in range(1, m) ]  # prime m: all of 1..m-1
    K = (m - 1) // 2
    return [[2 * carry(m, k, t) - 1 for t in units] for k in range(1, K + 1)], units

def rank_frac(rows):
    M = [[Fraction(x) for x in r] for r in rows]
    r = 0
    for c in range(len(M[0]) if M else 0):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        M = [row if i == r else [row[j] - row[c] / M[r][c] * M[r][j] for j in range(len(row))]
             for i, row in enumerate(M)]
        r += 1
    return r

def det_frac(rows, cols, M):
    sub = [[Fraction(M[i][j]) for j in cols] for i in rows]
    n = len(sub)
    det = Fraction(1)
    for c in range(n):
        piv = next((i for i in range(c, n) if sub[i][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            sub[c], sub[piv] = sub[piv], sub[c]
            det = -det
        det *= sub[c][c]
        for i in range(c + 1, n):
            f = sub[i][c] / sub[c][c]
            sub[i] = [sub[i][j] - f * sub[c][j] for j in range(n)]
    return det

for m in (3, 5, 7, 11, 13):
    W, units = signed_matrix(m)
    K = len(W)
    check(rank_frac(W) == K, f"m={m}: rank != K={K}")
    # find lexicographically first nonsingular K-column minor (prefer first K cols)
    minor = None
    for cols in combinations(range(m - 1), K):
        d = det_frac(range(K), cols, W)
        if d != 0:
            minor = (cols, d)
            break
    check(minor is not None, f"m={m}: no nonsingular minor?!")
    cols, d = minor
    print(f"[3] m={m}: K={K} FULL RANK; rows w_k on units 1..{m-1}:")
    for k, row in enumerate(W, start=1):
        print(f"      w_{k} = {row}")
    print(f"      nonsingular minor: unit columns t={[c+1 for c in cols]} (det = {d})")

# cross-check: ALL odd primes m <= 200 full rank (session stick_rank.py claim)
def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))
for m in (m for m in range(3, 201, 2) if is_prime(m)):
    W, _ = signed_matrix(m)
    check(rank_frac(W) == len(W), f"cross-check m={m}: not full rank")
print("[3b] cross-check OK: full rank K=(m-1)/2 for ALL odd primes m <= 200")

# ------------------------------------------------------- 4. m=8 degeneracy
units8 = [1, 3, 5, 7]
W8 = [[2 * carry(8, k, t) - 1 for t in units8] for k in (1, 2, 3)]
check(W8[2] == W8[0], f"m=8: w_3 != w_1 on units: {W8}")
check(rank_frac(W8) == 2, f"m=8: rank != 2: {W8}")
print(f"[4] m=8 units {units8}: w_1={W8[0]} w_2={W8[1]} w_3={W8[2]}  (w_3 == w_1, rank 2 < 3)")

if fails:
    print(f"{fails} FAILURES")
    sys.exit(1)
print("ALL EXACT CHECKS PASS")
