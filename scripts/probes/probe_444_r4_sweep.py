"""
Full r=4 (and r=3 recheck) line sweep using the validated FAST engine. Find true maximizer.
Excludes only the trivial constant direction x^0 (e=0 or f=0 makes one witness constant=1,
which is a degenerate "already a codeword" direction). Keeps x^{n/2}. By swap symmetry we
sweep e>f. Reports top lines, the maximizer, O_P, #bad, K, bad/K, and closed-form candidates.
"""
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_fast import census_all_lines

def sweep(n, r, exclude_const=True):
    K = (1 << r) * comb(n // 2, r)
    lines = []
    for e in range(n):
        for f in range(e):  # f < e (swap symmetry)
            if exclude_const and (e == 0 or f == 0):
                continue
            lines.append((e, f))
    t0 = time.time()
    res = census_all_lines(n, r, lines)
    dt = time.time() - t0
    table = []
    for ln, (nz, zb, op) in res.items():
        table.append((nz, int(zb), op, ln[0], ln[1]))
    table.sort(reverse=True)
    print(f"\n===== r={r} n={n} : {len(lines)} lines swept in {dt:.1f}s ; K={K} =====")
    print("  TOP 12 by #bad:")
    for (nz, zb, op, e, f) in table[:12]:
        d = gcd((e - f) % n, n)
        print(f"    (x^{e:>2},x^{f:>2}) d={d}: #bad={nz}(+{zb}z) O_P={op} bad/K={nz/K:.4f}")
    nz, zb, op, e, f = table[0]
    print(f"  >>> MAXIMIZER (x^{e},x^{f}): #bad={nz} O_P={op} K={K} bad/K={nz/K:.4f}")
    return n, r, e, f, nz, zb, op, K

if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else "16"
    if target == "16":
        # recheck r3 maximizer + full r4
        sweep(16, 3)
        sweep(16, 4)
    elif target == "32":
        sweep(32, 4)
    elif target == "32r3":
        sweep(32, 3)
    elif target == "64":
        sweep(64, 4)
