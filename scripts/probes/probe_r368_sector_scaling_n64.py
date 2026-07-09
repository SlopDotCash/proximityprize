#!/usr/bin/env python3
"""#466 R368: per-shape-sector mass scaling n=32 -> n=64 (test of the r367 Shkredov route).

Scans primes ≡ 1 mod 64, beta >= 3, computes exact excess via the r305 grouped evaluator,
and for the worst violators extracts the pair-mass spectrum by (support, height) of the
difference z. Route prediction: support-3 sector mass grows like n^(5/3) (ratio ~3.17 per
doubling), not n^2 (4) or n^3 (8).
"""
import sys, math
from collections import defaultdict

n = 64; m = n // 2
headroom = 45*n*n - 40*n
N3 = defaultdict(int)
for a in range(n):
    sa, ia = (1, a) if a < m else (-1, a - m)
    for b in range(n):
        sb, ib = (1, b) if b < m else (-1, b - m)
        for c in range(n):
            sc, ic = (1, c) if c < m else (-1, c - m)
            v = [0]*m; v[ia]+=sa; v[ib]+=sb; v[ic]+=sc
            N3[tuple(v)] += 1
e3_char0 = sum(c*c for c in N3.values())
assert e3_char0 == 15*n**3 - 45*n**2 + 40*n
items = list(N3.items())
print(f"n={n}: K={len(items)} vectors, headroom={headroom}", flush=True)

def is_prime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

lo, hi = int(sys.argv[1]), int(sys.argv[2])
for p in range(lo | 1, hi, 2):
    if p % n != 1 or not is_prime(p): continue
    for g in range(2, p):
        g0 = pow(g, (p-1)//n, p)
        if pow(g0, m, p) != 1: break
    powers = [pow(g0, j, p) for j in range(m)]
    groups = defaultdict(list)
    for w, c in items:
        e = sum(z*pw for z, pw in zip(w, powers)) % p
        groups[e].append((w, c))
    exc = 0
    coll = []
    for e, lst in groups.items():
        if len(lst) > 1:
            s = sum(c for _, c in lst)
            exc += s*s - sum(c*c for c, in [(c,) for _, c in lst])
            coll.append(lst)
    if exc > headroom:
        webs = defaultdict(int)
        for lst in coll:
            for i in range(len(lst)):
                for j in range(len(lst)):
                    if i != j:
                        z = tuple(x-y for x, y in zip(lst[j][0], lst[i][0]))
                        webs[(sum(1 for t in z if t), max(abs(t) for t in z))] += lst[i][1]*lst[j][1]
        beta = math.log(p)/math.log(n)
        spec = " ".join(f"s{k[0]}h{k[1]}:{v}" for k, v in sorted(webs.items()))
        print(f"VIOLATOR p={p} beta={beta:.3f} excess={exc} | {spec}", flush=True)
    elif exc:
        print(f"badprime p={p} excess={exc}", flush=True)
