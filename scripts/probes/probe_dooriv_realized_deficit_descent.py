#!/usr/bin/env python3
"""
Door-(iv) Lane-3 dilation route: MEASURE the actual per-level coherence deficit
delta_k in the real 2-dilation recursion on the thin 2-power subgroup, and test
whether the AVERAGE per-level deficit reaches the proven prize threshold (log2)/2
~= 0.3466 required by _DoorIVDeficitBudgetSublinearFloor.

Setup (matches the formalized object):
- mu_n = unique 2-power subgroup of F_p* of order n=2^a, p = 1 mod n, p >> n^3 (thin).
- worst frequency b* = argmax over F_p* of |eta_b| = |sum_{x in mu_n} e_p(b x)|.
- The 2-dilation descent splits mu_n into the index-2 subgroup mu_{n/2} (P0) and
  its coset (P1). Per-level "coherence" rho_k = |P0+P1|/(|P0|+|P1|), deficit delta_k = 1 - rho_k.
- The recursion descends: at level k we look at the order-2^{a-k} subgroup's worst-b split.

We measure delta_k along the descent at the GLOBAL worst b*, across n and primes,
to see whether the realized deficit budget S = sum delta_k is sub-linear (route DEAD,
cannot reach sqrt-scale) or reaches the (log2)/2 floor (route alive).
"""
import cmath, math

def find_prime(n, beta_min=3.0):
    # smallest prime p = 1 mod n with p >= n^beta_min
    target = int(n**beta_min)
    p = target - (target % n) + 1
    if p < target: p += n
    while True:
        if is_prime(p):
            return p
        p += n

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def subgroup(p, n):
    # generator of F_p*, then g^((p-1)/n) generates order-n subgroup
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x*h) % p
    return S, h

def primitive_root(p):
    if p == 2: return 1
    factors = set()
    phi = p-1
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            factors.add(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in factors):
            return g
    return None

def eta(b, S, p):
    s = 0j
    for x in S:
        s += cmath.exp(2j*math.pi*(b*x % p)/p)
    return s

def worst_b(S, p, h):
    # |eta_b| is constant on mu_n-cosets of F_p* (c in mu_n permutes S).
    # Scan one rep per coset via orbit-marking to cut the loop by factor n.
    seen = bytearray(p)
    best, bb = -1.0, None
    for b in range(1, p):
        if seen[b]:
            continue
        for c in S:
            seen[(b*c) % p] = 1
        v = abs(eta(b, S, p))
        if v > best:
            best, bb = v, b
    return bb, best

def descent_deficits(p, a, b):
    """At worst b, descend levels. Subgroup of order 2^(a-k) at level k.
    Split order-2m subgroup into order-m subgroup + coset, rho = |sum|/sum|piece|."""
    g = primitive_root(p)
    deficits = []
    for k in range(a):  # order = 2^(a-k), split into two order 2^(a-k-1)
        order = 2**(a-k)
        if order < 2: break
        h = pow(g, (p-1)//order, p)
        # subgroup elements
        elems = []
        x = 1
        for _ in range(order):
            elems.append(x); x = (x*h)%p
        half = order//2
        # index-2 subgroup = even powers, coset = odd powers
        P0 = sum(cmath.exp(2j*math.pi*(b*elems[2*i]%p)/p) for i in range(half))
        P1 = sum(cmath.exp(2j*math.pi*(b*elems[2*i+1]%p)/p) for i in range(half))
        denom = abs(P0)+abs(P1)
        rho = abs(P0+P1)/denom if denom>1e-12 else 1.0
        deficits.append(1.0-rho)
    return deficits

THRESH = math.log(2)/2
print(f"prize per-level deficit threshold (log2)/2 = {THRESH:.4f}")
print(f"{'a':>2} {'n':>5} {'p':>9} {'|eta_b*|':>9} {'avg_delta':>9} {'S=sum':>8} {'sqrt-scale?':>11}")
for a in range(3, 7):
    n = 2**a
    p = find_prime(n, 3.2)
    S, h = subgroup(p, n)
    b, mag = worst_b(S, p, h)
    defs = descent_deficits(p, a, b)
    Ssum = sum(defs)
    avg = Ssum/len(defs) if defs else 0.0
    # sqrt-scale reachable requires avg >= THRESH (sustained)
    verdict = "ALIVE" if avg >= THRESH else "DEAD(sublin)"
    print(f"{a:>2} {n:>5} {p:>9} {mag:>9.4f} {avg:>9.4f} {Ssum:>8.4f} {verdict:>11}")
    print(f"        deltas: {[round(d,4) for d in defs]}")
