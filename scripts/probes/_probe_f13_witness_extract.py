#!/usr/bin/env python3
"""Given the worst stack (s0,s1) found by the search, lift to explicit WORDS u0,u1
and, at the target radius, list every bad gamma with an explicit witness set S and
an interpolating codeword (a,b) for the line, so the Lean pin can use `decide`.
Run after _probe_f13_order6_deg2_deltastar search has dumped /tmp/f13_best.pkl.
Usage: python3 _probe_f13_witness_extract.py <delta_num> <delta_den> <m>
"""
import sys, pickle
from itertools import combinations
P, N, K = 13, 6, 2
XS = [pow(4, i, P) for i in range(N)]

def lineEval(a, b):
    return tuple((a + b * x) % P for x in XS)

CW = {(a, b): lineEval(a, b) for a in range(P) for b in range(P)}

def explain_on(w, S):
    for ab, cw in CW.items():
        if all(cw[i] == w[i] % P for i in S):
            return ab
    return None

# parity / syndrome lift
def rref(mat, p):
    m = [r[:] for r in mat]; rows = len(m); cols = len(m[0]); piv = []; r = 0
    for c in range(cols):
        pr = next((i for i in range(r, rows) if m[i][c] % p), None)
        if pr is None: continue
        m[r], m[pr] = m[pr], m[r]; inv = pow(m[r][c], p - 2, p); m[r] = [(x * inv) % p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] % p:
                f = m[i][c]; m[i] = [(a - f * b) % p for a, b in zip(m[i], m[r])]
        piv.append(c); r += 1
        if r == rows: break
    return m[:r], piv

def nullspace(mat, p):
    red, piv = rref(mat, p); cols = len(mat[0]); free = [c for c in range(cols) if c not in piv]; B = []
    for f in free:
        v = [0] * cols; v[f] = 1
        for r, c in enumerate(piv): v[c] = (-red[r][f]) % p
        B.append(v)
    return B

def solve_part(H, s, p):
    rows = [H[i] + [s[i]] for i in range(len(H))]; red, piv = rref(rows, p); n = len(H[0]); w = [0] * n
    for r, c in enumerate(piv): w[c] = red[r][n]
    return w

G = [[pow(x, j, P) for x in XS] for j in range(K)]
H = nullspace(G, P)

best, best_stack = pickle.load(open('/tmp/f13_best.pkl', 'rb'))
m = int(sys.argv[3])
s0, s1 = best_stack[m]
u0 = solve_part(H, list(s0), P)
u1 = solve_part(H, list(s1), P)
print("worst stack at m=%d (delta=(6-%d)/6):" % (m, m))
print("  u0 =", u0)
print("  u1 =", u1)

# big subsets of size >= m
def bad_with_witness(g):
    line = [(u0[i] + g * u1[i]) % P for i in range(N)]
    for size in range(N, m - 1, -1):
        for S in combinations(range(N), size):
            ab = explain_on(line, S)
            if ab is None:
                continue
            # need NOT (u0 explainable on S AND u1 explainable on S)
            e0 = explain_on(u0, S)
            e1 = explain_on(u1, S)
            if not (e0 is not None and e1 is not None):
                return S, ab, e0, e1
    return None

print("\nbad scalars with witnesses (witness set S, line codeword (a,b)):")
badset = []
for g in range(P):
    r = bad_with_witness(g)
    if r is not None:
        S, ab, e0, e1 = r
        badset.append(g)
        print(f"  gamma={g:2d}  S={S}  line=lineEval{ab}  (u0 expl {e0}, u1 expl {e1})")
print("\nbad set:", badset, " count=", len(badset))
print("Gbad =", "{" + ",".join(str(g) for g in badset) + "}")
