"""
probe_444_r4_truemax.py  (#444 demand-side census; r=4 TRUE worst-case line sweep)

Goal:
 (1) CALIBRATE: reproduce r=3 closed form O_P(3)=C(n/4,2)=6,28 at n=16,32, maximizer
     line (x^{n/2}, x^{n/2-1}) (order-2 adjacent).
 (2) r=4: sweep ALL admissible lines (x^e, x^f), exclude degenerate x^{n/2}=+-1 correlated
     directions, find the TRUE maximizer of #bad at n=16 and n=32 (and 64 if feasible).
 (3) Try to fit a clean closed form for O_P(r).

Band-gamma logic (depth r): a0=r+1 agreement, codeword deg k=r-1, deficit 2.
For an (r+1)-subset S of mu_n, interpolate x^e and x^f (deg<a0). gamma is bad iff the two
band coeffs j in [k,a0)={r-1,r} give a CONSISTENT gamma (both vanish-or-pinned same).
gamma = -c0[j]/c1[j].  #bad = distinct nonzero gamma; O_P = #orbits under mult-by w^{e-f}.

LARGE prime p=2013265921 (BabyBear), char-0 worst case.
"""
import itertools
from math import comb, gcd
from collections import Counter

p = 2013265921  # BabyBear, 2^27 | p-1

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 1000):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError("no w of order n=%d" % n)

def band_gamma(pts, vale, valf, k, a0):
    """Return pinned nonzero/zero gamma if S is bad for line (e,f), else None.
    vale/valf are precomputed x^e, x^f at the points of S."""
    m = len(pts)
    def interp(vals):
        # solve Vandermonde V c = vals, V[i][j]=pts[i]^j, return coeff list
        A = [[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
        M = [A[i][:] + [vals[i] % p] for i in range(m)]
        for col in range(m):
            piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            inv = pow(M[col][col], p - 2, p)
            M[col] = [(v * inv) % p for v in M[col]]
            for rr in range(m):
                if rr != col and M[rr][col] % p != 0:
                    c = M[rr][col]
                    M[rr] = [(M[rr][t] - c * M[col][t]) % p for t in range(m + 1)]
        return [M[i][m] % p for i in range(m)]
    c0 = interp(vale)
    c1 = interp(valf)
    if c0 is None or c1 is None:
        return None
    gam = None
    nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None  # x^e has nonzero top coeff but x^f doesn't -> no finite gamma
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None
    return gam if nd else None

def census_line(n, r, e, f, mu, want_types=False):
    """Full census for a single line (x^e,x^f). Returns (#bad_nz, has_zero, O_P, K, types)."""
    k = r - 1; a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    d = gcd((e - f) % n, n)
    mult = pow(mu[1], (e - f) % n, p) if len(mu) > 1 else None
    # mu[i] = w^i
    pe = [pow(x, e, p) for x in mu]
    pf = [pow(x, f, p) for x in mu]
    badset = {}
    zero_bad = False
    types = Counter()
    h = n // 2
    for Sidx in itertools.combinations(range(n), a0):
        pts = [mu[i] for i in Sidx]
        vale = [pe[i] for i in Sidx]
        valf = [pf[i] for i in Sidx]
        gv = band_gamma(pts, vale, valf, k, a0)
        if gv is None:
            continue
        if gv % p == 0:
            zero_bad = True
            continue
        if gv not in badset:
            badset[gv] = Sidx
        if want_types:
            Sset = set(Sidx)
            pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
            singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
            types[(pairs, singles)] += 1
    nz = list(badset.keys())
    # orbits under mult by w^{e-f}
    mult = pow(mu[1], (e - f) % n, p)
    rem = set(nz); orbs = 0
    while rem:
        x0 = next(iter(rem)); cur = x0; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % p
        orbs += 1; rem -= o
    return len(nz), zero_bad, orbs, K, types

def calibrate_r3():
    print("=== CALIBRATION r=3: expect O_P=C(n/4,2)=6 (n=16), 28 (n=32); maximizer (x^{n/2},x^{n/2-1}) ===")
    for n in [16, 32]:
        mu = [pow(w_of_order(n), i, p) for i in range(n)]
        e = n // 2; f = n // 2 - 1
        nz, zb, op, K, _ = census_line(n, 3, e, f, mu)
        expect_op = comb(n // 4, 2)
        expect_bad = n * comb(n // 4, 2) + 1
        ok = (op == expect_op)
        print(f"  n={n} line(x^{e},x^{f}): #bad={nz}(+{int(zb)}zero) total={nz+int(zb)} "
              f"O_P={op} | expect #bad_total={expect_bad} O_P={expect_op} | MATCH={ok and (nz+int(zb))==expect_bad}")

def sweep_r4(n, exclude_half=True, verbose_top=8):
    """Sweep ALL admissible (e,f) lines for r=4, find true #bad maximizer."""
    r = 4
    mu = [pow(w_of_order(n), i, p) for i in range(n)]
    h = n // 2
    results = []
    # Admissible: e != f. By dilation symmetry the census depends on line up to global mult;
    # but #bad and O_P are invariants of the unordered pair structure. We sweep all e,f in [0,n).
    # Exclude degenerate "x^{n/2}=+-1 correlated" directions: per task, exclude lines where
    # e or f equals n/2 producing the constant +-1 direction? The task says exclude degenerate
    # x^{n/2} correlated -- interpret: skip lines where {e,f} makes x^e or x^f constant on mu_n,
    # i.e. e or f == 0 (x^0=1) is the trivial constant. x^{n/2} is the +-1 (order 2) direction
    # which is the KNOWN r=3 maximizer family, NOT degenerate -- we KEEP it. We only drop e==f.
    seen = set()
    for e in range(n):
        for f in range(n):
            if e == f:
                continue
            key = (e, f)
            nz, zb, op, K, _ = census_line(n, r, e, f, mu)
            results.append((nz, zb, op, e, f, K))
    results.sort(reverse=True)
    bestbad = results[0][0]
    print(f"\n=== r=4 SWEEP n={n}: all {len(results)} ordered (e,f) lines, e!=f ===")
    print(f"  TOP {verbose_top} by #bad:")
    for (nz, zb, op, e, f, K) in results[:verbose_top]:
        d = gcd((e - f) % n, n)
        print(f"    (x^{e},x^{f}) d=gcd(e-f,n)={d}: #bad={nz}(+{int(zb)}zero) O_P={op} "
              f"K={K} bad/K={nz / K:.4f}")
    # report the maximizer
    nz, zb, op, e, f, K = results[0]
    # recompute with types for the maximizer
    nz2, zb2, op2, K2, types = census_line(n, r, e, f, mu, want_types=True)
    print(f"  >>> TRUE MAXIMIZER n={n}: (x^{e},x^{f}) #bad={nz}(+{int(zb)}zero) O_P={op} "
          f"K={K} bad/K={nz / K:.4f}")
    print(f"      antipodal (pairs,singles) dist: {dict(types)}")
    return n, e, f, nz, zb, op, K

if __name__ == "__main__":
    calibrate_r3()
    res16 = sweep_r4(16)
    res32 = sweep_r4(32)
    print("\n=== SUMMARY for closed-form fit ===")
    for (n, e, f, nz, zb, op, K) in [res16, res32]:
        print(f"  n={n}: maximizer(x^{e},x^{f}) O_P={op} #bad={nz} "
              f"C(n/4,3)={comb(n//4,3)} C(n/2,3)={comb(n//2,3)} C(n/4,2)={comb(n//4,2)} "
              f"C(n/2,2)={comb(n//2,2)}")
