#!/usr/bin/env python3
"""G90 follow-up: WHY is mult-by-g maximally scrambling, and can ANY multiplier fix it?

For each cell: enumerate ALL elements h of mu_n; for each, the induced permutation on
sorted b*mu_n; count adjacency-preserving pairs (pi(i+1)=pi(i)+1 cyclically) and
gap-preserving pairs. Prediction (rigidity dichotomy): gap preservation only for h=+-1;
adjacency preservation ~ 0 for all h notin {1,-1}, regardless of val(h).
Also: min val over mu_n \ {1, p-1} (the Cilleruelo-Garaev quantity) and K-sweep occupancy.
"""
import math
from probe_g90_spacing import is_prime, find_primes, subgroup, star_discrepancy_count

def analyze(p, n):
    S, g = subgroup(p, n)
    Sset = sorted(x % p for x in S)
    rank = {x: i for i, x in enumerate(Sset)}
    m = len(Sset)
    print(f"p={p} n={n}")
    minval = min(x for x in Sset if 1 < x < p-1)
    print(f"  min val over mu_n minus {{1,p-1}} = {minval}  (p/n={p/n:.1f}, sqrt(p)={math.sqrt(p):.1f})")
    rows = []
    for h in Sset:
        pi = [rank[h*x % p] for x in Sset]
        adj = sum(1 for i in range(m) if pi[(i+1) % m] == (pi[i]+1) % m)
        # reversed adjacency (orientation-reversing branch)
        adjrev = sum(1 for i in range(m) if pi[(i+1) % m] == (pi[i]-1) % m)
        # gap-preserving successor pairs: val gap of images equals val gap
        gp = 0
        for i in range(m):
            d = (Sset[(i+1) % m] - Sset[i]) % p
            dimg = (h*Sset[(i+1) % m] - h*Sset[i]) % p
            if dimg == d: gp += 1
        rows.append((h, adj, adjrev, gp))
    best = max(rows, key=lambda r: r[1] + r[2])
    ones = [r for r in rows if r[0] in (1, p-1)]
    others = [r for r in rows if r[0] not in (1, p-1)]
    maxadj_other = max(r[1] for r in others)
    maxadjrev_other = max(r[2] for r in others)
    maxgp_other = max(r[3] for r in others)
    print(f"  h=1: adj={ones[0][1]}/{m}; h=-1 rows: {[(r[1],r[2],r[3]) for r in rows if r[0]==p-1]}")
    print(f"  over h in mu_n minus {{1,-1}}: max adjacency-preserving pairs = {maxadj_other}/{m},"
          f" max reversed-adj = {maxadjrev_other}/{m}, max gap-preserving = {maxgp_other}/{m}")
    print(f"  best scrambler-resistant h: {best[0]} (val), adj+adjrev={best[1]+best[2]}")
    # small-val elements: does small val(h) help adjacency?
    smalls = sorted(Sset, key=lambda x: min(x, p-x))[:6]
    for h in smalls:
        r = [row for row in rows if row[0] == h][0]
        print(f"    val(h)={h} (sym {min(h,p-h)}): adj={r[1]} adjrev={r[2]} gap-pres={r[3]}")
    # K-sweep occupancy over all cosets: max deviation and Cilleruelo-Garaev room
    cosets = (p-1)//n
    seen = set(); reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        for x in Sset: seen.add(b*x % p)
        if len(reps) == cosets: break
    t2 = math.sqrt(n*math.log(p/n))
    print(f"  K-sweep (max over all {cosets} cosets): sqrt(n log(p/n))={t2:.2f}")
    for K in (2, 4, 8, 16, 32):
        if K > n: break
        worst = 0
        for b in reps:
            cnt = [0]*K
            for x in Sset: cnt[K*(b*x % p)//p] += 1
            dev = max(abs(c - n/K) for c in cnt)
            worst = max(worst, dev)
        # needed: K*eps + 2*pi*n/K <= t2  =>  eps <= (t2 - 2pi n/K)/K
        need = (t2 - 2*math.pi*n/K)/K
        print(f"    K={K:3d}: max|occ-n/K|={worst:7.2f}  n/K={n/K:7.2f}  "
              f"eps needed={need:7.2f} {'(K too small: osc cost dominates)' if need < 0 else ('MET' if worst <= need else 'not met')}")
    print()

for (p, n) in [(257, 16), (1153, 32), (2113, 64), (9473, 128), (65537, 256)]:
    analyze(p, n)
