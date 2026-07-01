# probe_444_r5_np.py -- numpy-vectorized #444 r=5 census, full line sweep.
#
# Per (r+1)-subset S precompute h_0..h_{n-1}(S) and e_1(S) ONCE.  Each line (e,f):
#   x^e interp:  top(deg r)=h_{e-r},  sub(deg r-1)=h_{e-r+1}-h_{e-r}*e_1.
# Band j in {r-1,r}: gamma=-x0/x1 must agree across the two j.  Vectorized consistency via
# CROSS-MULTIPLICATION (avoids per-subset inverse): the two (x0,x1) pairs are consistent iff
#   x0_sub*x1_top == x0_top*x1_sub (mod p)  AND zero-pattern compatible.  Products of values <p
#   (~2^31) are <2^62 -> fit in int64; we reduce mod p with numpy.  One inverse per surviving
#   subset to recover gamma for the orbit count.
#
# Validated vs exact Gaussian-elim probe (probe_444_r5_census) and r=3 calibration (O_P=6,28).

import itertools, sys, time
from math import comb, gcd
import numpy as np

p = 2013265921
P = np.int64(p)

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 500):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no w")

def mulmod(a, b):
    return (a.astype(np.int64) * b.astype(np.int64)) % P

def precompute(n, a0):
    w = w_of_order(n)
    mu = [pow(w, i, p) for i in range(n)]
    combos = list(itertools.combinations(range(n), a0))
    N = len(combos)
    maxdeg = n - 1
    H = np.zeros((N, maxdeg + 1), dtype=np.int64)
    E1 = np.zeros(N, dtype=np.int64)
    for idx, Sidx in enumerate(combos):
        S = [mu[i] for i in Sidx]
        coeffs = [1] + [0] * maxdeg
        for s in S:
            acc = 0
            for k in range(maxdeg + 1):
                acc = (acc * s + coeffs[k]) % p
                coeffs[k] = acc
        H[idx, :] = coeffs
        E1[idx] = sum(S) % p
    return mu, combos, H, E1, w

def col(H, deg, N):
    if deg < 0:
        return np.zeros(N, dtype=np.int64)
    if deg > H.shape[1] - 1:
        return np.zeros(N, dtype=np.int64)
    return H[:, deg]

def census_np(n, r, w, combos, H, E1, e, f):
    a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    N = len(combos)
    de, df = e - r, f - r
    h0t = col(H, de, N); h1t = col(H, df, N)
    h0t1 = col(H, de + 1, N); h1t1 = col(H, df + 1, N)
    x0_top = h0t % P
    x1_top = h1t % P
    x0_sub = (h0t1 - mulmod(h0t, E1)) % P
    x1_sub = (h1t1 - mulmod(h1t, E1)) % P
    # nondegenerate: at least one band coeff nonzero
    nd = (x0_sub | x1_sub | x0_top | x1_top) != 0
    # zero-compat: for each band j, NOT (x1==0 and x0!=0)
    ok_sub = ~((x1_sub == 0) & (x0_sub != 0))
    ok_top = ~((x1_top == 0) & (x0_top != 0))
    # consistency: gammas agree. Use cross-mult x0_sub*x1_top == x0_top*x1_sub.
    # This holds automatically when a band has x1==0 & x0==0 (contributes no constraint):
    #   then that side's gamma is "unpinned" -> cross-mult: x0_sub=0,x1_sub? careful.
    # Define: a band pins gamma only if x1!=0. If both bands pin, need equality.
    pin_sub = x1_sub != 0
    pin_top = x1_top != 0
    cross = (mulmod(x0_sub, x1_top) == mulmod(x0_top, x1_sub))
    both_pin = pin_sub & pin_top
    consistent = np.where(both_pin, cross, True)
    good = nd & ok_sub & ok_top & consistent
    # gamma value: from whichever band pins. gamma = -x0/x1.
    idxs = np.nonzero(good)[0]
    badset = set(); zero_bad = 0
    for i in idxs:
        if pin_top[i]:
            x0 = int(x0_top[i]); x1 = int(x1_top[i])
        elif pin_sub[i]:
            x0 = int(x0_sub[i]); x1 = int(x1_sub[i])
        else:
            # neither pins => both x1==0; nd true means some x0!=0 but ok_* would've failed -> skip
            continue
        g = (-x0 * pow(x1, p - 2, p)) % p
        if g == 0:
            zero_bad = 1
        else:
            badset.add(g)
    mult = pow(w, (e - f) % n, p)
    rem = set(badset); orbs = 0
    while rem:
        x = next(iter(rem)); cur = x; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % p
        orbs += 1; rem -= o
    return len(badset), zero_bad, orbs, K

def sweep(n, r, topk=14, lines=None):
    a0 = r + 1
    t0 = time.time()
    mu, combos, H, E1, w = precompute(n, a0)
    print(f"[precompute n={n} a0={a0}] {len(combos)} subsets in {time.time()-t0:.1f}s", flush=True)
    K = (1 << r) * comb(n // 2, r)
    src = lines if lines is not None else [(e, f) for e in range(n) for f in range(n) if e != f]
    res = []
    for (e, f) in src:
        nb, zb, op, _ = census_np(n, r, w, combos, H, E1, e, f)
        res.append((nb + zb, e, f, nb, zb, op, gcd((e - f) % n, n)))
    res.sort(key=lambda t: (t[0], t[5]), reverse=True)
    print(f"[SWEEP r={r} n={n}] K={K} lines={len(res)} total {time.time()-t0:.1f}s", flush=True)
    for row in res[:topk]:
        total, e, f, nb, zb, op, d = row
        print(f"  (x^{e:>2},x^{f:>2}) total={total:>7} nz={nb:>7} zero={zb} O_P={op:>6} d={d} bad/K={total/K:.4f}")
    b = res[0]
    print(f"  MAXIMIZER n={n}: (x^{b[1]},x^{b[2]}) total={b[0]} O_P={b[5]} K={K} bad/K={b[0]/K:.4f}", flush=True)
    return res, K

if __name__ == "__main__":
    args = sys.argv[1:]
    n = int(args[0]) if args else 16
    sweep(n, 5)
