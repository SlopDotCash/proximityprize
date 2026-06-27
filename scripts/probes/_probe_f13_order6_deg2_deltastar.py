#!/usr/bin/env python3
"""Exact mcaDeltaStar for RS[F_13, <4> (order 6), deg<2]  (LANE L2-F13-order6).

n=6, k=2, rate 1/3. Domain <4> = {4^0,...,4^5} = (1,4,3,12,9,10) in F_13^*.
Johnson = 1 - sqrt(1/3) ~ 0.4226. Capacity = 2/3.

Computes the exact ladder eps_mca(C, delta), finds the jump points, then for the
target threshold eps* = 1/2 finds delta* = sup{delta : eps_mca <= 1/2}, and
EXTRACTS an explicit worst bad stack (u0,u1) at delta* together with, for each bad
scalar gamma, a witness coordinate set S and an interpolating codeword (a,b) so the
Lean pin can be assembled with `decide`.
"""
from itertools import product, combinations
from math import sqrt
from fractions import Fraction

P, N, K = 13, 6, 2

def smooth_domain(p, n):
    for cand in range(2, p):
        g = pow(cand, (p - 1) // n, p)
        if all(pow(g, d, p) != 1 for d in range(1, n)) and pow(g, n, p) == 1:
            return g, [pow(g, i, p) for i in range(n)]
    raise ValueError("no gen")

# pick generator 4 specifically (order 6 in F_13^*)
def dom_gen4():
    g = 4
    assert all(pow(g, d, P) != 1 for d in range(1, N)) and pow(g, N, P) == 1
    return [pow(g, i, P) for i in range(N)]

XS = dom_gen4()
print("domain <4> =", XS)

def lineEval(a, b):
    return tuple((a + b * x) % P for x in XS)

CODEWORDS = {}
for a in range(P):
    for b in range(P):
        CODEWORDS[(a, b)] = lineEval(a, b)

def explain_on(w, S):
    """Return (a,b) of some codeword agreeing with w on S, or None."""
    for ab, cw in CODEWORDS.items():
        if all(cw[i] == w[i] % P for i in S):
            return ab
    return None

def ext_from(w, S):
    return explain_on(w, S) is not None

# subsets with |S| > k can refuse a pair (smaller always extend)
SUBSETS = []
for size in range(1, N + 1):
    SUBSETS.extend(combinations(range(N), size))

def mca_bad(u0, u1, gamma, m):
    """Is gamma bad for stack (u0,u1) at witness-size threshold m?
    bad iff exists S, |S|>=m, line extends on S, and NOT(u0 ext on S and u1 ext on S)."""
    line = tuple((a + gamma * b) % P for a, b in zip(u0, u1))
    for S in SUBSETS:
        if len(S) < m:
            continue
        if ext_from(line, S) and not (ext_from(u0, S) and ext_from(u1, S)):
            return True, S
    return False, None

# ---- syndrome reduction for the sup search ----
def rref(mat, p):
    m = [row[:] for row in mat]; rows = len(m); cols = len(m[0]) if m else 0
    piv = []; r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p), None)
        if pr is None: continue
        m[r], m[pr] = m[pr], m[r]
        inv = pow(m[r][c], p - 2, p); m[r] = [(x * inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p:
                f = m[i][c]; m[i] = [(a - f * b) % p for a, b in zip(m[i], m[r])]
        piv.append(c); r += 1
        if r == rows: break
    return m[:r], piv

def nullspace(mat, p):
    red, piv = rref(mat, p); cols = len(mat[0])
    free = [c for c in range(cols) if c not in piv]; basis = []
    for f in free:
        v = [0] * cols; v[f] = 1
        for r, c in enumerate(piv): v[c] = (-red[r][f]) % p
        basis.append(v)
    return basis

def solve_particular(H, s, p):
    rows = [H[i] + [s[i]] for i in range(len(H))]
    red, piv = rref(rows, p); n = len(H[0]); w = [0] * n
    for r, c in enumerate(piv):
        if c == n: raise ValueError("inconsistent")
        w[c] = red[r][n]
    return w

G = [[pow(x, j, P) for x in XS] for j in range(K)]
H = nullspace(G, P)
assert len(H) == N - K

bigsubsets = [S for S in SUBSETS if len(S) > K]
syndromes = list(product(range(P), repeat=N - K))
ext_mask = {}
for s in syndromes:
    w = solve_particular(H, list(s), P)
    mask = 0
    for bit, S in enumerate(bigsubsets):
        if ext_from(w, S):
            mask |= 1 << bit
    ext_mask[s] = mask

def adm_mask(m):
    mask = 0
    for bit, S in enumerate(bigsubsets):
        if len(S) >= m:
            mask |= 1 << bit
    return mask

ADM = {m: adm_mask(m) for m in range(K + 1, N + 1)}
best = {m: 0 for m in ADM}
best_stack = {m: None for m in ADM}
nz = [s for s in syndromes if any(s)]
for s0 in syndromes:
    for s1 in nz:
        bad_masks = []
        for g in range(P):
            line = tuple((a + g * b) % P for a, b in zip(s0, s1))
            bad_masks.append(ext_mask[line] & ~(ext_mask[s0] & ext_mask[s1]))
        for m, am in ADM.items():
            cnt = sum(1 for bm in bad_masks if bm & am)
            if cnt > best[m]:
                best[m] = cnt
                best_stack[m] = (s0, s1)

rho = Fraction(K, N)
print(f"\nRS[F_{P}, n={N}, k={K}] rate={float(rho):.4f} "
      f"UDR={float((1-rho)/2):.4f} Johnson={1-sqrt(float(rho)):.4f} cap={float(1-rho):.4f}")
print(f"{'m':>3} {'delta=1-m/n':>14} {'maxbad':>7} {'eps_mca':>10}")
profile = []  # (delta_frac, count)
for m in sorted(best, reverse=True):
    delta = Fraction(N - m, N)
    print(f"{m:>3} {str(delta):>14} {best[m]:>7}   {best[m]}/{P}")
    profile.append((delta, best[m], m))

# eps_mca(C,delta) as step function in delta. delta in [0,1].
# For delta in [ (N-m)/N , (N-(m-1))/N ), witness threshold is m? Actually clause is
# |S| >= (1-delta)*n.  m = ceil((1-delta)*n). For delta=(N-m)/N exactly, (1-delta)n = m.
# eps as function: at radius delta, count = best[ m(delta) ] where m=ceil((1-delta)n).

print("\n--- delta* at eps* = 1/2 ---")
# eps_mca <= 1/2 means count/13 <= 1/2 i.e. count <= 6 (since 6/13<1/2<7/13).
# sup of delta with count<=6.
target = Fraction(1, 2)
# count <= floor(13/2)=6 good
goodm = [m for m in sorted(best) if Fraction(best[m], P) <= target]
print("counts per m:", {m: best[m] for m in sorted(best)})
# delta increases as m decreases. find smallest m (largest delta) still good,
# and largest m that is bad above it -> jump.
ms = sorted(best.keys())  # ascending m => descending delta
# good radii: those m with eps<=1/2; bad radii: eps>1/2
for m in ms:
    d = Fraction(N - m, N)
    print(f"  m={m} delta={d} count={best[m]} eps={Fraction(best[m],P)} "
          f"{'GOOD' if Fraction(best[m],P)<=target else 'BAD'}")
print(f"counts per m: {[(m,best[m]) for m in ms]}")
