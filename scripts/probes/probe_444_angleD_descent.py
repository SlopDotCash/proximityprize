"""
probe_444_angleD_descent.py  (#444 Angle D -- DESCENT test r -> r-1 on mu_{n/2})

Two things:
(1) RECURSION CANDIDATES on the MAX over admissible lines:  Mbad(r,n) = max_line #bad.
    Test  Mbad(r,n) <= 2*Mbad(r-1, n/2)  and additive variants against measured table.
(2) STRUCTURAL DESCENT: for a bad (r+1)-subset S at depth r on a FIXED line, square the elements
    (z->z^2 maps mu_n -> mu_{n/2}) and ask whether the squared multiset / its support is bad at
    depth r-1 on a related line. We check the h_m generating-function descent:
        for antipodal-pair part, h_{2m}(pair{z,-z}) tracks h_m on z^2 in mu_{n/2}.

We import the fast measure() from probe_444_angleD_recursion.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter
sys.path.insert(0, "C:/Users/Administrator/arklib/scripts/probes")
from probe_444_angleD_recursion import measure, w_of_order, P, LINES

def maxline(n, r, fscan=None):
    """Scan admissible lines (x^e,x^f), 0<=f-r, e-r, e!=f, return the #bad-maximizing line and its
    O_P/#bad. To keep it cheap we scan a window of (e,f) with e in [r, ...] and small |e-f|, plus
    the known maximizer family. fscan: optional explicit list of (e,f)."""
    a0 = r+1
    best = None
    cands = []
    if fscan is not None:
        cands = list(fscan)
    else:
        # scan e in r..n-1 (deg e-r>=0 .. e<n meaningful), f in r..n-1, e!=f
        # window: restrict to keep runtime sane at n<=32: |e-f| up to ~6 and e,f in band
        for e in range(r, n):
            for f in range(r, n):
                if e == f: continue
                if e-r < 0 or f-r < 0: continue
                cands.append((e,f))
    for (e,f) in cands:
        res = measure(n, e, f, r)
        if res is None: continue
        score = res['nbad']
        if best is None or score > best[0]:
            best = (score, e, f, res)
    return best

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "max"
    if mode == "max":
        # full max-over-lines (expensive) only for n=16; for n=32 use the known maximizer + small window
        print("=== MAX over admissible lines:  Mbad(r,n) = max_line #bad,  O_P_max ===")
        results = {}
        for r in [3,4,5,6]:
            for n in [16]:
                b = maxline(n, r)
                if b is None: continue
                sc, e, f, res = b
                results[(r,n)] = (res['nbad'], res['OP'], res['K'], e, f)
                print(f"r={r} n={n}: MAX #bad={res['nbad']} O_P={res['OP']} at (x^{e},x^{f}) "
                      f"K={res['K']} bad/K={res['nbad']/res['K']:.4f}")
        print()
        print("=== RECURSION CANDIDATES (n=16 maxima vs n=8 maxima) ===")
        # need n=8 maxima too
        for r in [3,4]:
            b8 = maxline(8, r)
            if b8 is None:
                print(f"r={r} n=8: SKIP"); continue
            print(f"r={r} n=8: MAX #bad={b8[3]['nbad']} O_P={b8[3]['OP']} at (x^{b8[1]},x^{b8[2]}) K={b8[3]['K']}")
