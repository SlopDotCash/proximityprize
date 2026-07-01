"""
probe_444_angleD_descentmap.py  (#444 Angle D -- explicit descent map r->r-1 between varieties)

We test whether the bilinear Schur-ratio variety V(r,n) on the line (x^e,x^f) maps to V(r-1, n/2)
under a natural deficit-preserving operation, giving a recursion #bad(r,n) <= c * #bad(r-1,n/2).

Operations tested on each bad (r+1)-subset S (as exponent index set in Z_n):
  (A) "drop-one + halve": for each s in S, S\{s} has r elements; reduce exponents mod n/2 (i.e.
      project mu_n -> mu_{n/2} by z->z^... ) -- check membership in V(r-1,n/2) on a related line.
  (B) "square": z->z^2 maps mu_n onto mu_{n/2} (2:1). Apply to S (multiset of squares); if all r+1
      squares distinct that's an (r+1)-subset of mu_{n/2}=too big; so this drops a0 only if a pair
      collapses. Track collapse statistics.
  (C) Direct numeric recursion: compare measured #bad(r,n) to multiples of #bad(r-1,n/2) at the
      SAME named maximizer family AND at the max-over-lines.

This is exploratory; the load-bearing deliverable is the numeric recursion table + verdict.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter
sys.path.insert(0, "C:/Users/Administrator/arklib/scripts/probes")
from probe_444_angleD_recursion import measure, w_of_order, P, LINES

def line_for(n, r, family):
    return family(n)

if __name__ == "__main__":
    # Numeric recursion table: compare #bad(r,n) vs #bad(r-1, n/2) and vs 2*, and the
    # maximizer-family lines. We use the n=8,16,32 data we can compute.
    print("=== #bad / O_P table at the named maximizer families ===", flush=True)
    fams = LINES
    data = {}
    # cells: keep cheap. n=8 (all r), n=16 (all r), n=32 only r=3,4 (r5/r6 n32 too slow here)
    cells = [(3,8),(4,8),(3,16),(4,16),(5,16),(6,16),(3,32),(4,32)]
    for (r,n) in cells:
            if n < 2*r:   # need enough points / nonneg degs
                continue
            e, f = fams[r](n)
            if e < 0 or f < 0: continue
            res = measure(n, e, f, r)
            if res is None: continue
            data[(r,n)] = res
            print(f"r={r} n={n} (x^{e},x^{f}): #bad={res['nbad']} O_P={res['OP']} K={res['K']} "
                  f"d={res['d']}  #bad/n={res['nbad']/n:.3f}", flush=True)
    print()
    print("=== RECURSION CANDIDATE TESTS:  X(r,n) vs X(r-1, n/2),  X in {#bad, O_P} ===", flush=True)
    for X in ['nbad','OP']:
        print(f"-- X = {X} --", flush=True)
        for r in [4,5,6]:
            for n in [16,32]:
                if (r,n) in data and (r-1, n//2) in data:
                    cur = data[(r,n)][X]; prev = data[(r-1,n//2)][X]
                    ratio = cur/prev if prev else float('inf')
                    print(f"  {X}(r={r},n={n})={cur}  {X}(r-1={r-1},n/2={n//2})={prev}  ratio={ratio:.3f}", flush=True)
