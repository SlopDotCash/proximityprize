#!/usr/bin/env python3
"""#466 R365: test the r364 prediction — depth-3 badness ⟺ some kernel-lattice vector of
height ≤ 6 lies in the difference-class set Z3 (shape criterion), at n=16.

For each prime p ≡ 1 mod 16 in range: enumerate ALL z in Z3 (finite difference-class set
from the r305 classification) and check z(g) ≡ 0 mod p  [this reproduces excess>0], AND
independently enumerate ALL kernel vectors with l-inf ≤ 6 (meet-in-middle over dim 8) to
report lambda-inf and whether any height-≤6 kernel vector exists at all (Minkowski says yes
below 6^8). Output per prime: bad?, lambda-inf, #height≤6 kernel vectors, #in-Z3.
Prediction: bad ⟺ (#in-Z3 > 0); good primes below the norm frontier have kernel vectors of
height ≤ 6 whose SHAPE misses Z3.
"""
import sys
from collections import defaultdict
import numpy as np

n, m = 16, 8
# build N3 and Z3
N3 = defaultdict(int)
for a in range(n):
    sa, ia = (1, a) if a < m else (-1, a - m)
    for b in range(n):
        sb, ib = (1, b) if b < m else (-1, b - m)
        for c in range(n):
            sc, ic = (1, c) if c < m else (-1, c - m)
            v = [0]*m; v[ia]+=sa; v[ib]+=sb; v[ic]+=sc
            N3[tuple(v)] += 1
keys = list(N3.keys())
Z3 = set()
for i, w in enumerate(keys):
    for w2 in keys:
        z = tuple(a-b for a, b in zip(w2, w))
        if any(z): Z3.add(z)
print(f"|Z3| = {len(Z3)}", flush=True)

def is_prime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

lo, hi = int(sys.argv[1]), int(sys.argv[2])
mismatches = 0
rows = 0
for p in range(lo | 1, hi, 2):
    if p % 16 != 1 or not is_prime(p): continue
    for g in range(2, p):
        g0 = pow(g, (p-1)//n, p)
        if pow(g0, m, p) != 1: break
    powers = [pow(g0, j, p) for j in range(m)]
    # Z3 hits
    hits = sum(1 for z in Z3 if sum(zj*pw for zj, pw in zip(z, powers)) % p == 0)
    bad = hits > 0
    # meet-in-middle: all kernel vectors with entries in [-6,6]
    half = {}
    R = range(-6, 7)
    for a in R:
        for b in R:
            for c in R:
                for d in R:
                    s = (a*powers[0]+b*powers[1]+c*powers[2]+d*powers[3]) % p
                    half.setdefault(s, []).append((a,b,c,d))
    kcount = 0
    lam = 99
    for a in R:
        for b in R:
            for c in R:
                for d in R:
                    s = (-(a*powers[4]+b*powers[5]+c*powers[6]+d*powers[7])) % p
                    for left in half.get(s, []):
                        z = left + (a,b,c,d)
                        if any(z):
                            kcount += 1
                            lam = min(lam, max(abs(t) for t in z))
    ok = "OK " if (bad == (hits > 0)) else "??"
    pred_matches = True  # tautological half; the content is the good-prime side:
    rows += 1
    print(f"p={p:6d} bad={int(bad)} Z3hits={hits:3d} lambdaInf={lam} "
          f"heightLE6kernel={kcount}", flush=True)
print(f"done rows={rows}", flush=True)
