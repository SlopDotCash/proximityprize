#!/usr/bin/env python3
"""#466 G80U probe: pointwise-in-b orbit coincidence sums — max vs mean.

C(b) = sum_{d in H} #{y in H : arc(b d y) = arc(b y)}  (= same-arc pair count of b*H).
Grand identity (G80V): sum_b C(b) = n * sum_d R(d).  Here we measure the MAX over b,
its location, and the ratio max/mean — the exact max-vs-mean gap the wall lives in.
Also: is the argmax b related to H (e.g. b in H, or b in a small coset)?
"""
import math, sys

def order(a, p):
    o, x = 1, a % p
    while x != 1:
        x = x * a % p; o += 1
    return o

def run(n, p, K):
    g = next(c for c in range(2, p) if order(c, p) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H = []
    x = 1
    for _ in range(n):
        H.append(x); x = x * h % p
    Hset = set(H)
    arc = lambda v: K * v // p
    Cs = {}
    for b in range(1, p):
        arcs = [arc(b * y % p) for y in H]
        # pair count via occupancy second moment
        occ = {}
        for a in arcs:
            occ[a] = occ.get(a, 0) + 1
        Cs[b] = sum(c * c for c in occ.values())
    vals = list(Cs.values())
    mean = sum(vals) / len(vals)
    mx = max(vals)
    argmax = [b for b, c in Cs.items() if c == mx]
    inH = sum(1 for b in argmax if b in Hset)
    print(f"n={n} p={p} K={K}: mean C={mean:.1f} max C={mx} ratio={mx/mean:.2f} "
          f"#argmax={len(argmax)} argmax∩H={inH} n²/K+n={n*n/K + n:.1f}")

for (n, p, K) in [(8, 257, 8), (16, 257, 8), (16, 769, 16), (32, 1153, 16), (32, 1153, 32)]:
    run(n, p, K)
