#!/usr/bin/env python3
"""
G295 probe: the low-rank CORE covariance is a palindrome in the rank, A_r = A_{n+1-r},
and the two prize ranks are pinned to complementary high ranks (A_5 = A_{n-4}, A_6 = A_{n-5}).

Object (the current frontier CORE surrogate, G228..G293):
  W_G(x) = #{(y,z) in G^2 : 2y - z = x},   G = order-n multiplicative subgroup of F_p^*
  R_r(x) = (dp_r * dp_{r-1})(x),            dp_k[x] = #{k-subsets of G summing to x mod p}
  A_r    = p * sum_x W_G(x) R_r(x) - (sum W_G)(sum R_r)     (exact integer CORE covariance)

Verifies, in exact integer arithmetic (no floats):
  (1) For n EVEN (the sponsor 2-power regime): sigma = sum(G) = 0 mod p, -1 in G, W_G even,
      R_{n+1-r}(x) = R_r(-x), and A_r = A_{n+1-r} for all r in [2, n-1].
  (2) The exact prize-rank pins A_5 = A_{n-4}, A_6 = A_{n-5} on production cells.
  (3) The ZMod 17 Lean witness data: W17 even, R3(-x) = R6(x), A_3 = A_6 = -1344.

Each block hard-fails (SystemExit(1)) on any violation.
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


# ---- Block (1): even-n mechanism + palindrome ---------------------------------
# Cells kept build-light for the 4GB VPS: the full-rank palindrome check is O(n·p^2).
# n in {8,16,32} covers the sponsor 2-power regime; the identity is n-uniform.
even_cells = [(8, 17), (8, 113), (8, 257), (16, 97), (16, 113), (16, 257),
              (16, 1297), (32, 193)]
for (n, p) in even_cells:
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
    for r in range(1, n):
        R = adj_corr(hist[r], hist[r - 1], p)
        Rc = adj_corr(hist[n + 1 - r], hist[n - r], p) if 1 <= n + 1 - r <= n - 1 else None
        if Rc is not None and any(Rc[x] != R[(-x) % p] for x in range(p)):
            fail(f"R_(n+1-r)(x) != R_r(-x) at n={n} p={p} r={r}")
    for r in range(2, n):
        rp = n + 1 - r
        if 1 <= rp <= n - 1 and A_of(W, hist, p, r) != A_of(W, hist, p, rp):
            fail(f"palindrome A_r != A_(n+1-r) at n={n} p={p} r={r}")
print("(1) even-n mechanism + palindrome A_r=A_(n+1-r) verified on %d cells OK" % len(even_cells))


# ---- Block (2): exact prize-rank pins on production cells ----------------------
prize_cells = [(16, 1297), (32, 193), (16, 97)]
for (n, p) in prize_cells:
    G, W, hist = build(n, p)
    a5, a_nm4 = A_of(W, hist, p, 5), A_of(W, hist, p, n - 4)
    a6, a_nm5 = A_of(W, hist, p, 6), A_of(W, hist, p, n - 5)
    if a5 != a_nm4:
        fail(f"A_5 != A_(n-4) at n={n} p={p}: {a5} vs {a_nm4}")
    if a6 != a_nm5:
        fail(f"A_6 != A_(n-5) at n={n} p={p}: {a6} vs {a_nm5}")
    print("    n=%d p=%d: A_5=A_%d=%d, A_6=A_%d=%d" % (n, p, n - 4, a5, n - 5, a6))
print("(2) prize-rank pins A_5=A_(n-4), A_6=A_(n-5) verified OK")


# ---- Block (3): ZMod 17 Lean witness data -------------------------------------
n, p = 8, 17
G, W, hist = build(n, p)
W17_lean = [8, 3, 3, 4, 3, 4, 4, 4, 3, 3, 4, 4, 4, 3, 4, 3, 3]
R3_lean = [80, 96, 96, 90, 96, 90, 90, 90, 96, 96, 90, 90, 90, 96, 90, 96, 96]
R6_lean = [80, 96, 96, 90, 96, 90, 90, 90, 96, 96, 90, 90, 90, 96, 90, 96, 96]
if W != W17_lean:
    fail("W17 Lean vector mismatch")
R3 = adj_corr(hist[3], hist[2], p)
R6 = adj_corr(hist[6], hist[5], p)
if R3 != R3_lean or R6 != R6_lean:
    fail("R3/R6 Lean vector mismatch")
if any(R6[x] != R3[(-x) % p] for x in range(p)):
    fail("R6(x) != R3(-x)")
a3 = p * sum(W[x] * R3[x] for x in range(p)) - sum(W) * sum(R3)
a6 = p * sum(W[x] * R6[x] for x in range(p)) - sum(W) * sum(R6)
if not (a3 == a6 == -1344):
    fail(f"A_3/A_6 != -1344: {a3}, {a6}")
print("(3) ZMod 17 Lean witness: W17 even, R6(x)=R3(-x), A_3=A_6=%d OK" % a3)

print("\nALL PASS: rank-reflection palindrome, prize-rank pins, Lean witness.")
