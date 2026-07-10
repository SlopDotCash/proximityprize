#!/usr/bin/env python3
"""G90 cost-floor probe: the G80Z contrapositive gives ||eta_b|| <= K*eps(K) + 2*pi*n/K
where eps(K) = max over ALL cosets b and arcs j of |occ - n/K| (b-uniform sup certificate).
Measure eps(K) for all dyadic K, compute min_K of the bound, compare to eta_max and
t2 = sqrt(n log(p/n)). Also fit eps(K) against sqrt(n/K) (random-fluctuation shape) and
compute the same for iid random sets as control.
"""
import math, random
from probe_g90_spacing import find_primes, subgroup

def cell(p, n, seed=1):
    S, g = subgroup(p, n)
    cosets = (p-1)//n
    seen = set(); reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        for x in S: seen.add(b*x % p)
        if len(reps) == cosets: break
    t2 = math.sqrt(n*math.log(p/n))
    etamax = 0.0
    for b in reps:
        s = sum(complex(math.cos(2*math.pi*((b*x) % p)/p), math.sin(2*math.pi*((b*x) % p)/p)) for x in S)
        etamax = max(etamax, abs(s))
    print(f"p={p} n={n} cosets={cosets}  t2=sqrt(n log(p/n))={t2:.2f}  eta_max={etamax:.2f}")
    Ks, best, bestK = [], float('inf'), None
    K = 2
    rng = random.Random(seed)
    while K <= n:
        eps = 0.0
        for b in reps:
            cnt = [0]*K
            for x in S: cnt[K*((b*x) % p)//p] += 1
            eps = max(eps, max(abs(c - n/K) for c in cnt))
        bound = K*eps + 2*math.pi*n/K
        # random control: same #trials as cosets
        reps_r = 0.0
        for _ in range(min(cosets, 64)):
            T = rng.sample(range(p), n)
            cnt = [0]*K
            for x in T: cnt[K*x//p] += 1
            reps_r = max(reps_r, max(abs(c - n/K) for c in cnt))
        print(f"  K={K:4d}: eps={eps:7.2f} rand_eps={reps_r:7.2f} sqrt(n/K)={math.sqrt(n/K):5.2f}"
              f"  K*eps={K*eps:9.1f} osc=2pin/K={2*math.pi*n/K:8.1f}"
              f"  bound={bound:9.1f}  bound/t2={bound/t2:6.2f}")
        if bound < best: best, bestK = bound, K
        K *= 2
    print(f"  MIN over K: bound={best:.1f} at K={bestK}; best/t2={best/t2:.2f};"
          f" best/eta_max={best/etamax:.2f}; n^(2/3)={n**(2/3):.1f}; best/n^(2/3)={best/n**(2/3):.2f}")
    print()
    return best/t2

for (p, n) in [(257,16), (1153,32), (2113,64), (9473,128), (65537,256)]:
    cell(p, n)
# one bigger cell n=512, p ~ n^2
ps = find_primes(512, 512*512//2, 3*512*512, count=1)
for p in ps:
    cell(p, 512)
