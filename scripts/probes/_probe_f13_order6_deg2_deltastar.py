#!/usr/bin/env python3
"""Exact mcaDeltaStar for RS[F_13, <4> (order 6), deg<2]  (LANE L2-F13-order6).

n=6, k=2, rate 1/3. Domain <4> = {4^0,...,4^5} = (1,4,3,12,9,10) in F_13^*.
Johnson = 1 - sqrt(1/3) ~ 0.4226. Capacity = 2/3.

Syndrome-reduced exact sup. n-k=4 so 13^4=28561 syndromes; we precompute per
syndrome its extension-bitmask over the |S|>k subsets, then for the worst-case
search exploit that mcaEvent at threshold m depends on the line syndrome
s0+g*s1 and the joint stack mask. We vectorize the inner gamma/subset work.
"""
from itertools import product, combinations
from math import sqrt
from fractions import Fraction
import numpy as np

P, N, K = 13, 6, 2

def dom_gen4():
    g = 4
    assert all(pow(g, d, P) != 1 for d in range(1, N)) and pow(g, N, P) == 1
    return [pow(g, i, P) for i in range(N)]

XS = dom_gen4()
print("domain <4> =", XS, flush=True)

def lineEval(a, b):
    return tuple((a + b * x) % P for x in XS)

CODEWORDS = [lineEval(a, b) for a in range(P) for b in range(P)]

# subsets of size > k (only these can refuse)
BIGSUB = [S for size in range(K + 1, N + 1) for S in combinations(range(N), size)]
NB = len(BIGSUB)
print(f"#big subsets = {NB}", flush=True)

# precompute, for a word, the extension bitmask over BIGSUB
def ext_mask_word(w):
    mask = 0
    for bit, S in enumerate(BIGSUB):
        ok = False
        for cw in CODEWORDS:
            if all(cw[i] == w[i] for i in S):
                ok = True; break
        if ok:
            mask |= 1 << bit
    return mask

# ---- syndrome machinery ----
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
Hmat = np.array(H, dtype=np.int64)  # (n-k) x n

# Enumerate all syndromes, build coset representative word and ext mask.
syndromes = list(product(range(P), repeat=N - K))
SI = {s: i for i, s in enumerate(syndromes)}
NS = len(syndromes)
print(f"#syndromes = {NS}", flush=True)

# mask per syndrome as a Python int bitmask over BIGSUB
maskint = [0] * NS
for i, s in enumerate(syndromes):
    w = solve_particular(H, list(s), P)
    maskint[i] = ext_mask_word(w)

# admissible subset bitmask per threshold m
def adm_int(m):
    msk = 0
    for bit, S in enumerate(BIGSUB):
        if len(S) >= m:
            msk |= 1 << bit
    return msk

ADM = {m: adm_int(m) for m in range(K + 1, N + 1)}

# line syndrome index table: for fast lookup, precompute s0+g*s1 -> index.
# We'll do the sup search but vectorize over gamma and subsets.
syn_arr = np.array(syndromes, dtype=np.int64)  # NS x (n-k)

best = {m: 0 for m in ADM}
best_stack = {m: None for m in ADM}

# Direction representatives: s1 up to nonzero scalar (first nonzero entry == 1).
# Scaling s1 by c reparametrizes the line gamma -> gamma*c (a bijection on F_p),
# so bad-count over gamma is invariant. This cuts the s1 loop by factor (p-1).
def is_rep(s):
    for x in s:
        if x % P != 0:
            return x % P == 1
    return False
nz_idx = [i for i, s in enumerate(syndromes) if is_rep(s)]
print(f"#s1 direction reps = {len(nz_idx)}", flush=True)
gammas = np.arange(P).reshape(-1, 1)  # P x 1

# Precompute index of every syndrome tuple for line lookup
def syn_index(vec):
    # vec : (n-k,) ints mod P
    key = 0
    for x in vec:
        key = key * P + int(x % P)
    return key

# Build flat index map keyed by base-P encoding
idx_map = np.empty(P ** (N - K), dtype=np.int64)
for i, s in enumerate(syndromes):
    key = 0
    for x in s:
        key = key * P + x
    idx_map[key] = i

powP = np.array([P ** j for j in range(N - K - 1, -1, -1)], dtype=np.int64)

ADM_keys = sorted(ADM.keys())
ADM_list = [ADM[m] for m in ADM_keys]

# Precompute line-index table per direction lazily; iterate over all s0 (NS) and
# direction reps. Pure-int bitmask inner loop (fast).
# For each direction j, precompute for every s0 the P line indices via idx_map.
syn_int = np.array(syndromes, dtype=np.int64)
keys_all = (syn_int * powP[None, :]).sum(axis=1)  # NS -> base-P key of each syndrome
assert (idx_map[keys_all] == np.arange(NS)).all()

total_dirs = len(nz_idx)
for di, j in enumerate(nz_idx):
    s1v = syn_arr[j]
    mask1 = maskint[j]
    s1key = int((s1v * powP).sum())  # not directly usable; recompute lines properly
    # line indices for ALL s0, ALL gamma: shape NS x P
    # lines[s0,g] = s0 + g*s1
    lines = (syn_int[:, None, :] + gammas[None, :, :] * s1v[None, None, :]) % P  # NS x P x (n-k)
    lkeys = (lines * powP[None, None, :]).sum(axis=2)  # NS x P
    lidx_all = idx_map[lkeys]  # NS x P
    lidx_list = lidx_all.tolist()
    for ci in range(NS):
        joint = maskint[ci] & mask1
        njoint = ~joint
        row = lidx_list[ci]
        # bad bitmask per gamma (computed once)
        bbits = [maskint[r] & njoint for r in row]
        for k in range(len(ADM_keys)):
            am = ADM_list[k]
            cnt = 0
            for b in bbits:
                if b & am:
                    cnt += 1
            if cnt > best[ADM_keys[k]]:
                m = ADM_keys[k]
                best[m] = cnt
                best_stack[m] = (syndromes[ci], syndromes[j])
    if di % 100 == 0:
        print(f"  ..dir {di}/{total_dirs} best={ {m:best[m] for m in ADM_keys} }", flush=True)

rho = Fraction(K, N)
print(f"\nRS[F_{P}, n={N}, k={K}] rate={float(rho):.4f} "
      f"UDR={float((1-rho)/2):.4f} Johnson={1-sqrt(float(rho)):.4f} cap={float(1-rho):.4f}", flush=True)
print(f"{'m':>3} {'delta=(N-m)/N':>14} {'maxbad':>7} {'eps_mca':>10}")
for m in sorted(best, reverse=True):
    delta = Fraction(N - m, N)
    print(f"{m:>3} {str(delta):>14} {best[m]:>7}   {best[m]}/{P}  stack={best_stack[m]}")

target = Fraction(1, 2)
print("\n--- per-m good/bad at eps*=1/2 (count<=6 good) ---")
for m in sorted(best):
    d = Fraction(N - m, N)
    print(f"  m={m} delta={d} count={best[m]} eps={Fraction(best[m],P)} "
          f"{'GOOD' if Fraction(best[m],P)<=target else 'BAD'}")
