"""Definitive full r=4 sweep at n=32 (all admissible lines), using validated np2 engine."""
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_np2 import census_np2

def run(n, r):
    K = (1 << r) * comb(n // 2, r)
    lines = [(e, f) for e in range(n) for f in range(e) if e != 0 and f != 0]
    print(f"n={n} r={r}: sweeping {len(lines)} lines (e>f, excl x^0), K={K}", flush=True)
    t0 = time.time()
    res = census_np2(n, r, lines, collect_orbit=True, progress=True)
    dt = time.time() - t0
    table = sorted(((nz, int(zb), op, e, f) for (e, f), (nz, zb, op) in res.items()), reverse=True)
    print(f"DONE in {dt:.0f}s. TOP 15 by #bad:", flush=True)
    for (nz, zb, op, e, f) in table[:15]:
        d = gcd((e - f) % n, n)
        print(f"  (x^{e:>2},x^{f:>2}) e-f={(e-f)%n} d={d}: #bad={nz}(+{zb}z) O_P={op} bad/K={nz/K:.4f}", flush=True)
    nz, zb, op, e, f = table[0]
    print(f">>> MAXIMIZER n={n} r={r}: (x^{e},x^{f}) #bad={nz}(+{zb}z) O_P={op} K={K} bad/K={nz/K:.4f}", flush=True)
    # also report all distinct (#bad, O_P) seen for the top tier
    from collections import Counter
    cnt = Counter((nz, op) for (nz, zb, op, e, f) in table[:30])
    print("  top-30 (#bad,O_P) multiplicities:", dict(cnt), flush=True)
    return n, r, e, f, nz, zb, op, K

if __name__ == "__main__":
    run(32, 4)
