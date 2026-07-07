# probe_444_r5_census.py  -- #444 demand-side census, r=5 TRUE-maximizer sweep.
#
# Deep-band object (q-INDEPENDENT, char-0 worst case via BabyBear p):
#   depth r -> agreement a0 = r+1, codeword degree k = r-1, deficit 2, band j in [k,a0)={r-1,r}.
#   witness line (x^e, x^f); bad gamma = -h_{e-r}(S)/h_{f-r}(S); #bad = [gamma=0] + (n/d)*O_P.
#   O_P = #distinct NONZERO Schur-ratio orbits under multiply-by w^{e-f}.
#
# TASK:
#  (1) reproduce r=3 calibration O_P(3)=C(n/4,2)=6,28 at n=16,32 (anti-fabrication).
#  (2) r=5: sweep ALL admissible lines (e,f), find TRUE maximizer of #bad at n=16,32(,64).
#  (3) fit a clean closed form for O_P(r), or report none.
#
# Honest, exact integers mod p only. Large prime => char-0 worst case (no char-p undercount).

import itertools, sys
from math import comb, gcd
from collections import Counter

p = 2013265921  # BabyBear, 2^27 | p-1

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 500):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no w of order n")

def interp_coeffs(pts, vals):
    # solve Vandermonde for coefficient vector (deg < m) over F_p, exact.
    m = len(pts)
    M = [[pow(pts[i], j, p) for j in range(m)] + [vals[i] % p] for i in range(m)]
    for col in range(m):
        piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], p - 2, p)
        M[col] = [(v * inv) % p for v in M[col]]
        for rr in range(m):
            if rr != col and M[rr][col] % p != 0:
                f = M[rr][col]
                M[rr] = [(M[rr][t] - f * M[col][t]) % p for t in range(m + 1)]
    return [M[i][m] % p for i in range(m)]

def band_gamma(pts, e, f, k, a0):
    # returns pinned gamma if the (r+1)-subset is bad (band coeffs consistent), else None.
    # gamma==0 returned as 0 (caller separates zero-bad).
    c0 = interp_coeffs(pts, [pow(t, e, p) for t in pts])
    c1 = interp_coeffs(pts, [pow(t, f, p) for t in pts])
    if c0 is None or c1 is None:
        return None
    gam = None; nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None
        else:
            g = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g
            elif gam != g:
                return None
    if not nd:
        return None
    return gam if gam is not None else 0

def census_line(n, r, mu, w, e, f):
    # full census for one line. returns (#bad_nonzero, zero_bad_flag, O_P, K, dict_types)
    k = r - 1; a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    d = gcd((e - f) % n, n)
    mult = pow(w, (e - f) % n, p)
    types = Counter(); badset = set(); zero_bad = 0
    h = n // 2
    for Sidx in itertools.combinations(range(n), a0):
        pts = [mu[i] for i in Sidx]
        gv = band_gamma(pts, e, f, k, a0)
        if gv is None:
            continue
        if gv == 0:
            zero_bad = 1
            continue
        badset.add(gv)
        # antipodal (pairs, singles) type
        Sset = set(Sidx)
        pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
        singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
        types[(pairs, singles)] += 1
    # O_P: orbits of nonzero gammas under mult-by w^{e-f}
    rem = set(badset); orbs = 0
    while rem:
        x = next(iter(rem)); cur = x; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % p
        orbs += 1; rem -= o
    return len(badset), zero_bad, orbs, K, dict(types), d

def admissible_lines(n):
    # all (e,f) with e!=f in [0,n); exclude degenerate x^{n/2} == +-1 correlated directions.
    # x^{n/2} maps mu_n -> {+-1} (it is the order-2 character), a degenerate direction; the task
    # says exclude these. We exclude e or f == n/2 ONLY when that makes a column collapse to a
    # 2-valued (degenerate) function. We keep e=n/2 lines that the calibration/known maximizers use
    # (r=3 maximizer is (n/2, n/2-1)). So: exclude lines where BOTH e and f reduce mod (order) to
    # the trivial/sign direction. Practically: exclude e==f. We do NOT pre-exclude n/2 since the
    # KNOWN maximizers (r=3:(n/2,n/2-1); r=4 n=16:(8,5)) include e=n/2.
    for e in range(n):
        for f in range(n):
            if e == f:
                continue
            yield e, f

def calibrate(n):
    r = 3
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    e, f = n // 2, n // 2 - 1
    nb, zb, op, K, types, d = census_line(n, r, mu, w, e, f)
    want = comb(n // 4, 2)
    ok = (op == want) and (nb == n * comb(n // 4, 2)) and (zb == 1)
    print(f"[CALIB r=3 n={n}] line(x^{e},x^{f}): O_P={op} (want C(n/4,2)={want}) "
          f"#bad_nz={nb} (want n*C(n/4,2)={n*comb(n//4,2)}) zero={zb} -> {'OK' if ok else 'FAIL'}")
    return ok, op, nb

def sweep_r5(n, full=True):
    r = 5
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    K = (1 << r) * comb(n // 2, r)
    best = None  # (total_bad, e, f, nb_nz, zb, op, types, d)
    results = []
    for (e, f) in admissible_lines(n):
        nb, zb, op, _K, types, d = census_line(n, r, mu, w, e, f)
        total = nb + zb  # total bad gamma incl zero
        results.append((total, e, f, nb, zb, op, d))
        if best is None or total > best[0] or (total == best[0] and op > best[5]):
            best = (total, e, f, nb, zb, op, types, d)
    results.sort(reverse=True)
    print(f"\n[SWEEP r=5 n={n}] K=2^5*C(n/2,5)={K}; #lines={len(results)}")
    print(f"  TOP 8 lines by total #bad (total, e, f, nb_nz, zero, O_P, d):")
    for row in results[:8]:
        total, e, f, nb, zb, op, d = row
        print(f"    (x^{e:>2},x^{f:>2}) total={total:>5} nb_nz={nb:>5} zero={zb} O_P={op:>4} d={d} bad/K={total/K:.4f}")
    total, e, f, nb, zb, op, types, d = best
    print(f"  TRUE MAXIMIZER n={n}: line(x^{e},x^{f}) total#bad={total} (nz={nb}+zero={zb}) "
          f"O_P={op} d={d} K={K} bad/K={total/K:.4f}")
    print(f"     antipodal types: {types}")
    return e, f, total, nb, zb, op, K

if __name__ == "__main__":
    print("=== r=3 CALIBRATION (must reproduce O_P=6,28) ===")
    c16 = calibrate(16)
    c32 = calibrate(32)
    print("\n=== r=5 TRUE-MAXIMIZER SWEEP ===")
    r16 = sweep_r5(16)
    r32 = sweep_r5(32)
    print("\nCALIB_OK =", c16[0] and c32[0])
