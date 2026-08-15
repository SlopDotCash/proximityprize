#!/usr/bin/env python3
"""G102F probe: additive lift amplification on the G80Q terminal object.

Measures, per cell (n, beta):
  - rho(c) = #(H cap (H+c)) statistics over c in (H-H)\{0}: rho_max, rho_mean, top counts
  - per-z incident-ratio counts r_z at windows W in [sqrt(p), p/8] and the
    amplification counts A_z = #{c in (H-H)\0 : c*z in Strip(2W)} (and full-sweep 4W cap)
  - Capstone A: sdp(W)^2 <= n*sdp(W) + 4*rho_max*n^2*W  (valid 4W < p)
  - Capstone B: sdp(W)^2 <= n*sdp(W) + n^2*sdp(2W)      (valid 4W < p)
  - comparison of bound sqrt-forms vs trivial caps and vs truth.
"""
import math, random, sys
from collections import Counter

random.seed(20260710)

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def find_prime(n, beta):
    """smallest prime p = 1 mod n with p >= n^beta"""
    target = int(n**beta)
    p = target - (target % n) + 1
    while not (p % n == 1 and is_prime(p)):
        p += n
    return p

def mu_n(n, p):
    """the multiplicative subgroup of order n (n | p-1)"""
    while True:
        x = random.randrange(2, p)
        h = pow(x, (p-1)//n, p)
        # check exact order n (n is 2-power in our cells)
        if h != 1 and pow(h, n//2, p) != 1:
            break
    H = set()
    v = 1
    for _ in range(n):
        H.add(v); v = v*h % p
    assert len(H) == n
    return H

def minabs(x, p):
    x %= p
    return x if 2*x <= p else x - p

def cell(n, beta, n_cosets=6):
    p = find_prime(n, beta)
    H = mu_n(n, p)
    Hl = sorted(H)
    # rho(c) over c in (H-H)\0
    rho = Counter()
    for d in Hl:
        for dp in Hl:
            if d != dp:
                rho[(d-dp) % p] += 1
    rho_vals = sorted(rho.values(), reverse=True)
    rho_max = rho_vals[0]
    rho_mean = sum(rho_vals)/len(rho_vals)
    diffset = set(rho.keys())
    K_saddle = max(2, int(math.sqrt(2*math.pi*n/math.log(p))))
    W_prize = p // K_saddle
    print(f"\n=== cell n={n} beta={beta} p={p} |H-H\\0|={len(diffset)} "
          f"rho_max={rho_max} rho_mean={rho_mean:.2f} rho_top5={rho_vals[:5]} "
          f"K_saddle={K_saddle} W_prize={W_prize}")
    # W grid: sqrt(p)/2 .. p/8 geometric + prize
    Ws = []
    w = int(math.sqrt(p))//2
    while w < p//8:
        Ws.append(w); w = int(w*2)
    Ws.append(p//8 - 1)
    if 4*W_prize < p: Ws.append(W_prize)
    Ws = sorted(set(Ws))
    worstA = 0.0; worstB = 0.0
    for ci in range(n_cosets):
        b = random.randrange(1, p)
        C = [b*y % p for y in Hl]
        # per-z difference lists (minabs of u-z over u in C, u != z)
        # sdp(W) = sum_z r_z(W)
        absdiffs_per_z = []
        for z in C:
            ds = sorted(abs(minabs(u-z, p)) for u in C if u != z)
            absdiffs_per_z.append(ds)
        import bisect
        def r_z(zi, W): return bisect.bisect_right(absdiffs_per_z[zi], W)
        def sdp(W): return sum(r_z(i, W) for i in range(n))
        for W in Ws:
            if 4*W >= p: continue
            s = sdp(W); s2 = sdp(2*W)
            lhs = s*s
            rhsA = n*s + 4*rho_max*n*n*W
            rhsB = n*s + n*n*s2
            ratA = lhs/rhsA if rhsA else 0
            ratB = lhs/rhsB if rhsB else 0
            worstA = max(worstA, ratA); worstB = max(worstB, ratB)
            if ci == 0:
                # per-z amplification check on the 3 heaviest z
                heavy = sorted(range(n), key=lambda i: -r_z(i, W))[:3]
                amp_notes = []
                ok = True
                for zi in heavy:
                    r = r_z(zi, W)
                    if r < 2: continue
                    z = C[zi]
                    A = sum(1 for c in diffset if abs(minabs(c*z, p)) <= 2*W)
                    if r*(r-1) > rho_max*A: ok = False
                    amp_notes.append(f"r={r} A={A} r(r-1)/A={r*(r-1)/A:.2f} A/4W={A/(4*W):.3f}")
                unif = 2*W*n*n/p
                boundA_lin = (n + math.sqrt(n*n + 16*rho_max*n*n*W))/2
                triv = min(n*(n-1), 2*W*n)
                print(f"  W={W:>10} ({W/math.sqrt(p):7.2f}*sqrt(p)) sdp={s:>7} "
                      f"unif={unif:9.1f} boundA={boundA_lin:10.1f} triv={triv:>9} "
                      f"ratA={ratA:.3f} ratB={ratB:.3f} perz_ok={ok} {amp_notes[:2]}")
    print(f"  worst capstoneA lhs/rhs = {worstA:.4f}   worst capstoneB lhs/rhs = {worstB:.4f}")
    return rho_max

for (n, beta) in [(16,2.0),(16,3.0),(32,2.0),(32,2.5),(64,2.0),(64,2.5),(128,2.0)]:
    cell(n, beta)
print("\nDone.")
