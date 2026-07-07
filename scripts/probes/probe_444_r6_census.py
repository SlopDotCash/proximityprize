"""
probe_444_r6_census.py  (#444 deep-band demand census, r=6)

Methodology mirrors scripts/probes/probe_444_antipodal_law.py and
scripts/probes/genlaw/o165_census_demand/badscalar_demand.py EXACTLY:
  - depth r: a0 = r+1 (agreement), k = r-1 (codeword deg bound). band j in [k,a0) = {r-1, r}.
  - for an (r+1)-subset S of mu_n, interpolate x^e and x^f (deg-coeff vector via Gaussian elim
    mod p). A bad gamma exists iff the two band coeffs (deg r-1 and deg r) of x^e + gamma x^f
    both can be made to vanish CONSISTENTLY: gamma pinned by one band degree, constrained by the
    other. gamma = -c0[j]/c1[j], must agree across j in {r-1, r}, and be nondegenerate.
  - #bad = distinct nonzero pinned gamma (+ [zero gamma reachable]).
  - O_P = #distinct nonzero gamma ORBITS under multiply-by-w^{e-f} (dilation eigenvector).

LARGE prime p = BabyBear = 2013265921 (2^27 | p-1) => char-0 worst case.
"""
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
    raise RuntimeError("no w of order %d" % n)

def interp(pts, vals):
    """Return coeff vector [c0..c_{m-1}] of the deg<m interpolant of (pts->vals) mod p, or None."""
    m = len(pts)
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

def band_gamma(pts, e, f, k, a0):
    """Pinned bad gamma for line (x^e, x^f) on point-set pts, band j in [k,a0). None if no bad."""
    c0 = interp(pts, [pow(t, e, p) for t in pts])
    c1 = interp(pts, [pow(t, f, p) for t in pts])
    if c0 is None or c1 is None:
        return None
    gam = None; nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None  # u0 has nonzero band coeff that u1 cannot cancel => inconsistent
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None  # inconsistent across the two band degrees
    return gam if nd else None

def census(n, r, e, f, mu=None, w=None):
    """Full census for one line (x^e,x^f) at depth r. Returns dict of stats."""
    if mu is None:
        w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    k = r - 1; a0 = r + 1
    K = (1 << r) * comb(n // 2, r)
    d = gcd((e - f) % n, n); mult = pow(w, (e - f) % n, p)
    types = Counter(); badset = {}; zero_bad = False
    for Sidx in itertools.combinations(range(n), a0):
        pts = [mu[i] for i in Sidx]
        gv = band_gamma(pts, e, f, k, a0)
        if gv is None:
            continue
        if gv % p == 0:
            zero_bad = True; continue
        if gv not in badset:
            badset[gv] = Sidx
    nz = list(badset.keys())
    rem = set(nz); orbs = 0
    while rem:
        x0 = next(iter(rem)); cur = x0; o = set()
        for _ in range(n):
            o.add(cur); cur = cur * mult % p
        orbs += 1; rem -= o
    return dict(nbad=len(nz), zero=int(zero_bad), OP=orbs, d=d, K=K,
               ratio=(len(nz) / K if K else 0.0))

# ---------------------------------------------------------------------------
# (1) CALIBRATION: r=3 must give O_P=C(n/4,2) = 6 (n=16), 28 (n=32).
#     Maximizer line = order-2 ADJACENT (x^{n/2}, x^{n/2-1}).
# ---------------------------------------------------------------------------
def calibrate():
    print("=== CALIBRATION r=3: expect O_P=C(n/4,2)=6 (n=16), 28 (n=32); #bad=n*C(n/4,2)+1 ===")
    ok = True
    for n in [16, 32]:
        w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
        e = n // 2; f = n // 2 - 1
        st = census(n, 3, e, f, mu, w)
        exp_OP = comb(n // 4, 2)
        exp_bad = n * comb(n // 4, 2) + 1   # includes the +1 (gamma=0 bad)
        got_bad_incl = st['nbad'] + st['zero']
        good = (st['OP'] == exp_OP) and (got_bad_incl == exp_bad)
        ok = ok and good
        print(f"  n={n} line(x^{e},x^{f}): O_P={st['OP']} (exp {exp_OP}) "
              f"#bad+zero={got_bad_incl} (exp {exp_bad})  d={st['d']}  -> {'OK' if good else 'MISMATCH'}")
    print(f"  CALIBRATION {'PASSED' if ok else 'FAILED'}")
    return ok

# ---------------------------------------------------------------------------
# (1b) CROSS-CHECK r=4 against task-stated values (n=16:(8,5)->#bad145,O_P9; n=32:(16,13)->577,O_P18)
# ---------------------------------------------------------------------------
def crosscheck_r4():
    print("=== CROSS-CHECK r=4 (task-stated reference lines) ===")
    for (n, e, f, eb, eo) in [(16, 8, 5, 145, 9), (32, 16, 13, 577, 18)]:
        w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
        st = census(n, 4, e, f, mu, w)
        incl = st['nbad'] + st['zero']
        print(f"  n={n} line(x^{e},x^{f}): #bad(nz)={st['nbad']} +zero={st['zero']} (incl={incl}, ref {eb}) "
              f"O_P={st['OP']} (ref {eo})  K={st['K']} bad/K={st['ratio']:.4f}")

# ---------------------------------------------------------------------------
# (2) r=6 FULL SWEEP: find the TRUE worst-case line (x^e,x^f) maximizing #bad.
#     Exclude degenerate x^{n/2}=+-1 correlated directions is NOT done -- the task says
#     "exclude the degenerate x^{n/2}=+-1 correlated directions" meaning skip lines where one
#     exponent makes x^e identically a constant scaling of x^f; concretely skip e==f. We DO allow
#     e or f = n/2 (the resonant order-2 direction is exactly where the r=3 maximizer lives).
#     We sweep all unordered {e,f}, 0<=f<e<n, and report the top lines.
# ---------------------------------------------------------------------------
def sweep_r(n, r, topk=12, restrict=None):
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    results = []
    pairs = restrict if restrict is not None else [
        (e, f) for e in range(1, n) for f in range(0, e)]
    for (e, f) in pairs:
        st = census(n, r, e, f, mu, w)
        results.append(((e, f), st))
    results.sort(key=lambda kv: (kv[1]['nbad'], kv[1]['OP']), reverse=True)
    K = (1 << r) * comb(n // 2, r)
    print(f"=== r={r} SWEEP n={n}  (K=2^{r}*C({n//2},{r})={K}) ; top {topk} lines by #bad ===")
    for (e, f), st in results[:topk]:
        print(f"  line(x^{e:>2},x^{f:>2}) d={st['d']:>2}: #bad={st['nbad']:>6} +zero={st['zero']} "
              f"O_P={st['OP']:>5}  bad/K={st['ratio']:.4f}")
    best = results[0]
    return best, results

if __name__ == "__main__":
    import time
    calibrate()
    print()
    crosscheck_r4()
    print()
    t0 = time.time()
    sweep_r(16, 6, topk=15)
    print(f"  [n=16 r=6 sweep took {time.time()-t0:.1f}s]")


# ---------------------------------------------------------------------------
# (2b) n=32 r=6: too many subsets (C(32,7)=3.36M) to sweep ALL lines. The n=16 r=6 winners
#      are d=2 lines (x^10,x^8),(x^12,x^10) with #bad=112,O_P=14 -- the resonant line MOVED off
#      the order-2 adjacent (x^{n/2},x^{n/2-1}) that won at r=3. We test the structurally-motivated
#      candidate lines at n=32: all small-gap lines |e-f| in {1,2,3,4} near the top, plus the r=3/r=4
#      reference directions. We collect per-line #bad/O_P. One line ~ 3.36M * 7x7 interp.
# ---------------------------------------------------------------------------
def candidates_n32_r6():
    n = 32
    cands = []
    # mirror the n=16 winners scaled: e-f=2 lines across the range, both-even and mixed
    for e in range(6, 32):
        for f in [e-1, e-2, e-3, e-4]:
            if f >= 0:
                cands.append((e, f))
    # dedupe, keep e>f
    seen = set(); out = []
    for (e, f) in cands:
        key = (e, f)
        if key not in seen and e != f:
            seen.add(key); out.append((e, f))
    return n, out
