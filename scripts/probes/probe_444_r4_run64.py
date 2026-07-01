"""
n=64 r=4 TARGETED census (full sweep infeasible). Computes the predicted maximizer family
(x^{n/2+2}, x^{n/4+1}) and a representative basket of other lines to (a) confirm local/global
maximality and (b) get the third O_P(4) data point to pin the closed form.

Predicted maximizer n=64: (x^34, x^17), e-f=17=n/4+1.
Basket: all e-f in {n/4-1, n/4+1, ...} variants for the family + a coarse grid of other lines.
Uses validated np2 engine (one subset-pass over all basket lines together).
"""
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_np2 import census_np2

def run(n, r):
    K = (1 << r) * comb(n // 2, r)
    h = n // 2; q = n // 4
    # include the predicted max + a dense neighborhood + a coarse global grid
    cand = set()
    cand.add((h + 2, q + 1))            # predicted maximizer (34,17)
    cand.add((q + 1, h + 2))            # swap (not needed but harmless; engine uses e>f? no, free)
    # neighborhood of predicted max
    for de in range(-3, 4):
        for df in range(-3, 4):
            e = (h + 2 + de) % n; f = (q + 1 + df) % n
            if e != f and e != 0 and f != 0:
                cand.add((max(e, f), min(e, f)))
    # all lines with e-f in the observed resonant differences, sweeping the base fully
    for diff in [q - 1, q + 1, q, q + 2, q - 2, 3, 5]:
        for base in range(n):
            e = (base + diff) % n; f = base
            if e != f and e != 0 and f != 0:
                cand.add((max(e, f), min(e, f)))
    # coarse global guard grid (sparser) to catch a surprise maximizer elsewhere
    for e in range(1, n, 5):
        for f in range(1, e, 5):
            cand.add((e, f))
    lines = sorted(cand)
    print(f"n={n} r={r}: {len(lines)} candidate lines, K={K}", flush=True)
    t0 = time.time()
    res = census_np2(n, r, lines, collect_orbit=True, progress=True)
    dt = time.time() - t0
    table = sorted(((nz, int(zb), op, e, f) for (e, f), (nz, zb, op) in res.items()), reverse=True)
    print(f"DONE in {dt:.0f}s. TOP 15:", flush=True)
    for (nz, zb, op, e, f) in table[:15]:
        d = gcd((e - f) % n, n)
        print(f"  (x^{e:>2},x^{f:>2}) e-f={(e-f)%n} d={d}: #bad={nz}(+{zb}z) O_P={op} bad/K={nz/K:.4f}", flush=True)
    nz, zb, op, e, f = table[0]
    print(f">>> BEST n={n} r={r} (over basket): (x^{e},x^{f}) #bad={nz}(+{zb}z) O_P={op} K={K} bad/K={nz/K:.5f}", flush=True)
    print(f"   #bad == n*O_P+? : n*O_P={n*op}, #bad+zero={nz+zb}", flush=True)

if __name__ == "__main__":
    run(64, 4)
