# probe_444_r5_fast.py -- fast #444 demand-side census via symmetric-function shortcut.
#
# For S of size a0=r+1, interpolant of x^e has:
#   deg-r coeff   = h_{e-r}(S)                          (complete homogeneous symmetric poly)
#   deg-(r-1) coeff = h_{e-r+1}(S) - h_{e-r}(S)*e_1(S)  (verified exactly vs Gaussian elim)
# Band consistency over j in {r-1, r}: gamma pinned by deg-r coeff = -h_{e-r}/h_{f-r}, and the
# deg-(r-1) coeffs must give the SAME gamma.  This avoids the (r+1)x(r+1) solve per subset.
#
# We need complete-homogeneous h_d(S) for d in {e-r, e-r+1, f-r, f-r+1} and e_1(S)=sum(S).
# Build them incrementally over subsets is hard; instead compute per subset with small-degree
# generating-function recurrences (degrees are tiny since e,f < n).

import itertools, sys
from math import comb, gcd
from collections import Counter

p = 2013265921

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 500):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no w")

def hvec(S, maxdeg):
    # complete homogeneous symmetric polys h_0..h_maxdeg of S, exact mod p, via prod 1/(1-s t).
    if maxdeg < 0:
        return [1]
    coeffs = [1] + [0] * maxdeg
    for s in S:
        acc = 0
        for k in range(maxdeg + 1):
            acc = (acc * s + coeffs[k]) % p
            coeffs[k] = acc
    return coeffs

def census_line_fast(n, r, mu, w, e, f):
    k = r - 1; a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    mult = pow(w, (e - f) % n, p)
    d = gcd((e - f) % n, n)
    de = e - r; df = f - r            # leading h-degrees
    maxdeg = max(de, df) + 1
    badset = set(); zero_bad = 0; types = Counter()
    h = n // 2
    for Sidx in itertools.combinations(range(n), a0):
        S = [mu[i] for i in Sidx]
        H = hvec(S, max(maxdeg, 0))
        def hh(dd):
            if dd < 0: return 0
            if dd >= len(H): return None  # shouldn't happen given maxdeg
            return H[dd]
        h0_top = hh(de)        # deg-r coeff of x^e interpolant
        h1_top = hh(df)        # deg-r coeff of x^f interpolant
        e1 = sum(S) % p
        h0_sub = ((hh(de + 1) or 0) - (h0_top or 0) * e1) % p   # deg-(r-1) coeff x^e
        h1_sub = ((hh(df + 1) or 0) - (h1_top or 0) * e1) % p   # deg-(r-1) coeff x^f
        # band j=r: coeff pair (h0_top, h1_top); j=r-1: (h0_sub, h1_sub).
        # need consistent gamma with -x0/x1 across both j (x1=h1_*, x0=h0_*).
        gam = None; nd = False
        ok = True
        for (x0, x1) in ((h0_sub, h1_sub), (h0_top, h1_top)):
            x0 %= p; x1 %= p
            if x0 or x1:
                nd = True
            if x1 == 0:
                if x0:
                    ok = False; break
            else:
                g = (-x0 * pow(x1, p - 2, p)) % p
                if gam is None:
                    gam = g
                elif gam != g:
                    ok = False; break
        if not ok or not nd:
            continue
        gv = gam if gam is not None else 0
        if gv == 0:
            zero_bad = 1
            continue
        badset.add(gv)
        Sset = set(Sidx)
        pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
        singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
        types[(pairs, singles)] += 1
    rem = set(badset); orbs = 0
    while rem:
        x = next(iter(rem)); cur = x; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % p
        orbs += 1; rem -= o
    return len(badset), zero_bad, orbs, K, dict(types), d

def calibrate(n, r=3):
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    e, f = n // 2, n // 2 - 1
    nb, zb, op, K, types, d = census_line_fast(n, r, mu, w, e, f)
    want = comb(n // 4, 2)
    ok = (op == want) and (nb == n * want) and (zb == 1)
    print(f"[CALIB r=3 n={n}] (x^{e},x^{f}): O_P={op}(want {want}) nb={nb}(want {n*want}) zero={zb} -> {'OK' if ok else 'FAIL'}")
    return ok

def admissible(n):
    for e in range(n):
        for f in range(n):
            if e != f:
                yield e, f

def sweep(n, r, lines=None, topk=10):
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    K = (1 << r) * comb(n // 2, r)
    src = lines if lines is not None else list(admissible(n))
    res = []
    for (e, f) in src:
        nb, zb, op, _K, types, d = census_line_fast(n, r, mu, w, e, f)
        res.append((nb + zb, e, f, nb, zb, op, d, types))
    res.sort(key=lambda t: (t[0], t[5]), reverse=True)
    print(f"\n[SWEEP r={r} n={n}] K={K} lines={len(res)}")
    for row in res[:topk]:
        total, e, f, nb, zb, op, d, _ = row
        print(f"  (x^{e:>2},x^{f:>2}) total={total:>6} nz={nb:>6} zero={zb} O_P={op:>5} d={d} bad/K={total/K:.4f}")
    best = res[0]
    print(f"  MAXIMIZER: (x^{best[1]},x^{best[2]}) total={best[0]} O_P={best[5]} K={K} bad/K={best[0]/K:.4f}")
    print(f"     types: {best[7]}")
    return best, K

if __name__ == "__main__":
    args = sys.argv[1:]
    print("=== CALIBRATION ===")
    calibrate(16); calibrate(32)
    if "n16" in args or not args:
        sweep(16, 5)
    if "n32" in args:
        sweep(32, 5)
    if "n64" in args:
        sweep(64, 5)
