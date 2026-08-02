#!/usr/bin/env python3
"""
G321 probe: the rank-reflection palindrome A_r = A_{n+1-r} at the (n=12, p=13) cell.

Object (same frontier CORE surrogate as G295, G228..G293):
  W_G(x) = #{(y,z) in G^2 : 2y - z = x},   G = order-n multiplicative subgroup of F_p^*
  R_r(x) = (dp_r * dp_{r-1})(x),            dp_k[x] = #{k-subsets of G summing to x mod p}
  A_r    = p * sum_x W_G(x) R_r(x) - (sum W_G)(sum R_r)     (exact integer CORE covariance)

Verifies, in exact integer arithmetic (no floats), at the (n=12, p=13) cell:
  (1) sigma = sum(G) = 0 mod 13, -1 in G, W_G even.
  (2) R_8(x) = R_5(-x) (the rank-reflection identity at late-Newton ranks 5 and n+1-5=8).
  (3) A_5 = A_8 = -12 (the palindrome pinned, exact integer).
  (4) Reproduces the G295 (n=8, p=17) Lean witness (sanity: this is the same algorithm).

The (n=12, p=13) cell is special: G = F_13^* = {1, 2, ..., 12} (full multiplicative group,
since 12 | 12), and the gate W is almost-constant: W[0] = 12, W[x != 0] = 11. The
adjacent-rank rows R_5 and R_8 are also almost-constant: R[0] = 30156, R[x != 0] = 30157.
A_5 = A_8 = -12 is therefore a tiny integer — easier to audit than the G295 (n=8, p=17)
witness's A_3 = A_6 = -1344.

Stdlib only. No sympy, no numpy, no float. Each block hard-fails (SystemExit(1)) on any
violation.
"""
from __future__ import annotations


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def prime_factors(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int) -> list[int]:
    root = primitive_root(p)
    z = pow(root, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def dp_hist(G: list[int], p: int, R: int) -> list[list[int]]:
    hist = [[0] * p for _ in range(R + 1)]
    hist[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for k in range(min(R, used), 0, -1):
            src = hist[k - 1]
            dst = hist[k]
            for s in range(p):
                v = src[s]
                if v:
                    dst[(s + x) % p] += v
    return hist


def adj_corr(dpr: list[int], dprm1: list[int], p: int) -> list[int]:
    R = [0] * p
    for s in range(p):
        a = dpr[s]
        if a:
            for t in range(p):
                b = dprm1[t]
                if b:
                    R[(s - t) % p] += a * b
    return R


def build(n: int, p: int):
    G = subgroup(p, n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    hist = dp_hist(G, p, n)
    return G, W, hist


def A_of(W, hist, p, r):
    R = adj_corr(hist[r], hist[r - 1], p)
    return p * sum(W[x] * R[x] for x in range(p)) - sum(W) * sum(R)


def fail(msg):
    print("FAIL:", msg)
    raise SystemExit(1)


# ---- Block (1): even-cell mechanism + palindrome on the (n=12, p=13) cell ----
n, p = 12, 13
if n % 2 != 0:
    fail(f"cell n={n} not even")
if not is_prime(p) or (p - 1) % n != 0:
    fail(f"bad cell {n},{p}")
G, W, hist = build(n, p)
sigma = sum(G) % p
if sigma != 0:
    fail(f"sigma != 0 at n={n} p={p}: {sigma}")
if (p - 1) not in G:
    fail(f"-1 not in G at n={n} p={p}")
if any(W[x] != W[(-x) % p] for x in range(p)):
    fail(f"W not even at n={n} p={p}")
# Full palindrome sweep on this cell
for r in range(1, n):
    R = adj_corr(hist[r], hist[r - 1], p)
    rc = n + 1 - r
    if 1 <= rc <= n - 1:
        Rc = adj_corr(hist[rc], hist[rc - 1], p)
        if any(Rc[x] != R[(-x) % p] for x in range(p)):
            fail(f"R_(n+1-r)(x) != R_r(-x) at n={n} p={p} r={r}")
        if A_of(W, hist, p, r) != A_of(W, hist, p, rc):
            fail(f"palindrome A_r != A_(n+1-r) at n={n} p={p} r={r}: "
                 f"{A_of(W, hist, p, r)} vs {A_of(W, hist, p, rc)}")
print(f"(1) even-n mechanism + palindrome A_r=A_(n+1-r) verified on (n=12, p=13) OK; "
      f"|G|={len(G)} sum(G) mod p = {sigma}")


# ---- Block (2): late-Newton rank pin A_5 = A_8 = -12 on (n=12, p=13) ----
a5 = A_of(W, hist, p, 5)
a8 = A_of(W, hist, p, 8)
if a5 != a8:
    fail(f"A_5 != A_8 at n={n} p={p}: {a5} vs {a8}")
if a5 != -12:
    fail(f"A_5 != -12 at n={n} p={p}: {a5}")
print(f"(2) late-Newton rank pin A_5 = A_8 = {a5} (n+1-5 = 8) verified on (n=12, p=13) OK")


# ---- Block (3): ZMod 13 Lean witness data ----
# R5 and R8 vectors at (n=12, p=13) — the kernel stub pins these exactly.
R5 = adj_corr(hist[5], hist[4], p)
R8 = adj_corr(hist[8], hist[7], p)
W13_lean = list(W)
R5_lean = list(R5)
R8_lean = list(R8)
# Reflection identity check: R8[x] == R5[-x]
if any(R8_lean[x] != R5_lean[(-x) % p] for x in range(p)):
    fail("R8(x) != R5(-x)")
# The kernel stub will pin these three vectors, plus W13_even and A13_5 = A13_8 = -12.
print(f"(3) ZMod 13 Lean witness: W13 = {W13_lean}")
print(f"    R5  = {R5_lean}")
print(f"    R8  = {R8_lean}")
print(f"    R8(x) = R5(-x)  ✓")
print(f"    A_5 = A_8 = -12 ✓")


# ---- Block (4): G295 (n=8, p=17) sanity check (same algorithm, no drift) ----
n, p = 8, 17
G17, W17, hist17 = build(n, p)
W17_known = [8, 3, 3, 4, 3, 4, 4, 4, 3, 3, 4, 4, 4, 3, 4, 3, 3]
R3_known = [80, 96, 96, 90, 96, 90, 90, 90, 96, 96, 90, 90, 90, 96, 90, 96, 96]
if W17 != W17_known:
    fail(f"W17 mismatch vs G295 Lean vector")
R3 = adj_corr(hist17[3], hist17[2], p)
R6 = adj_corr(hist17[6], hist17[5], p)
if R3 != R3_known or R6 != R3_known:
    fail(f"R3/R6 mismatch vs G295 Lean vector")
a3 = A_of(W17, hist17, p, 3)
a6 = A_of(W17, hist17, p, 6)
if not (a3 == a6 == -1344):
    fail(f"A_3/A_6 != -1344 in G295 reproduction: {a3}, {a6}")
print(f"(4) G295 (n=8, p=17) reproduction: A_3 = A_6 = -1344 ✓ (algorithm matches)")


print("\nALL PASS: G321 (n=12, p=13) cell — palindrome A_r = A_{n+1-r}, late-Newton pin A_5 = A_8 = -12, "
      "G295 algorithm matches.")
