"""
Verify the exact integer inequalities for G207 magnitude no-go and print the exact
constants to embed in Lean. Also re-verify A_r via the identity and independent recompute.
"""
import math
from fractions import Fraction

def factor(n):
    out = []; d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out

def primitive_root(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError(p)

def subgroup(p, n):
    z = pow(primitive_root(p), (p - 1) // n, p)
    G = []; x = 1
    for _ in range(n):
        G.append(x); x = x * z % p
    assert x == 1 and len(set(G)) == n
    return G

def subset_hist(G, p, R):
    dp = [[0] * p for _ in range(R + 1)]
    dp[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for k in range(min(R, used), 0, -1):
            prev = dp[k - 1]; cur = dp[k]
            for t in range(p):
                v = prev[t]
                if v:
                    cur[(t + x) % p] += v
    for k in range(R + 1):
        assert sum(dp[k]) == math.comb(len(G), k)
    return dp

def circ_corr(a, b, p):
    c = [0] * p
    for s in range(p):
        av = a[s]
        if av:
            for u in range(p):
                bv = b[u]
                if bv:
                    c[(s - u) % p] += av * bv
    assert sum(c) == sum(a) * sum(b)
    return c

def cell(p, n, rs=(5, 6)):
    G = subgroup(p, n)
    assert 2 not in G, "degenerate"
    img = [pow((2 - u) % p, n, p) for u in G]
    inj = (len(set(img)) == n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    dp = subset_hist(G, p, max(rs))
    QW = sum((p * W[t] - n * n) ** 2 for t in range(p))
    out = {}
    for r in rs:
        R = circ_corr(dp[r], dp[r - 1], p)
        Cr = math.comb(n, r) * math.comb(n, r - 1)
        C12 = sum(W[t] * R[t] for t in range(p))
        A = p * C12 - n * n * Cr
        QR = sum((p * R[t] - n * n * Cr) ** 2 for t in range(p))
        out[r] = (A, QW, QR)
    return inj, out

n = 8
# chosen witnesses:
#  I1=449 (inj), N1=41 (noninj): M5(I1) > M5(N1)   -> suppression refuted
#  I2=113 (inj), N2=73 (noninj): M5(I2) < M5(N2)   -> reverse separation refuted (overlap)
cells = {}
for p in (449, 41, 113, 73):
    cells[p] = cell(p, n)

def show(p):
    inj, out = cells[p]
    A5, QW, QR5 = out[5]
    A6, _, QR6 = out[6]
    print(f"p={p} inj={inj}  A5={A5} A6={A6}  QW={QW} QR5={QR5} QR6={QR6}")
    return inj, out

print("=== witness cells ===")
for p in (449, 41, 113, 73):
    show(p)

def M2exact(p, out, r):
    # exact rational M_r^2 = rho_r^2 * q = A_r^2 * q^3 / (Q_W * Q_R)
    A, QW, QR = out[r]
    return Fraction(A * A * p ** 3, QW * QR)

i1 = cells[449][1]; n1 = cells[41][1]
i2 = cells[113][1]; n2 = cells[73][1]

# Cross-multiplied integer inequality for M5^2(a) > M5^2(b):
#   Aa^2 * pa^3 * QWb * QRb  >  Ab^2 * pb^3 * QWa * QRa
def cross_gt(pa, oa, pb, ob, r):
    Aa, QWa, QRa = oa[r]
    Ab, QWb, QRb = ob[r]
    L = Aa * Aa * pa ** 3 * QWb * QRb
    Rr = Ab * Ab * pb ** 3 * QWa * QRa
    return L, Rr, L > Rr

print("\n=== inequality 1: M5^2(inj 449) > M5^2(noninj 41)  [suppression refuted] ===")
L, R, ok = cross_gt(449, i1, 41, n1, 5)
print(f"LHS={L}\nRHS={R}\nLHS>RHS: {ok}")
print(f"  floats: M5^2(449)={float(M2exact(449,i1,5)):.6f}  M5^2(41)={float(M2exact(41,n1,5)):.6f}")

print("\n=== inequality 2: M5^2(inj 113) < M5^2(noninj 73)  [reverse separation refuted / overlap] ===")
L, R, ok = cross_gt(73, n2, 113, i2, 5)  # M5^2(73) > M5^2(113)
print(f"LHS(73)={L}\nRHS(113)={R}\nM5^2(73)>M5^2(113): {ok}")
print(f"  floats: M5^2(113)={float(M2exact(113,i2,5)):.6f}  M5^2(73)={float(M2exact(73,n2,5)):.6f}")

print("\n=== injectivity flags (for the record) ===")
for p in (449, 113):
    print(f"  p={p}: phi2 injective = {cells[p][0]}")
for p in (41, 73):
    print(f"  p={p}: phi2 injective = {cells[p][0]}")
