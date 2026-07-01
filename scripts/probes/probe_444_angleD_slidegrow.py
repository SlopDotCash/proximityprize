"""
probe_444_angleD_slidegrow.py  (#444 Angle D -- does the same-line depth-slide ratio grow in n?)

At n=16 the line (x^{n/2+4},x^{n/2+2}) = (x^12,x^10) had #bad slide r4->r5->r6 = 24,40,112 with
ratios 1.67, 2.80 (GROWING, exceeds 2). If this ratio grows with n, NO constant-multiplier
recursion #bad(r) <= c*#bad(r-1) (same line) can hold => Angle-D constant recursion is dead.

Test the analogous family at n=32: line (x^{n/2+4},x^{n/2+2}) = (x^20,x^18), depths r=4,5,6.
Also test the cross-group recursion #bad(r,n) vs #bad(r-1,n/2) on the *matched* family
(x^{n/2+4},x^{n/2+2}) at (r,n)=(6,32) vs (5,16) vs (4,8) to see the multiplier trend.
"""
import sys
from math import gcd, comb
sys.path.insert(0, "C:/Users/Administrator/arklib/scripts/probes")
from probe_444_angleD_recursion import measure

if __name__ == "__main__":
    print("=== n=32 same-line slide on (x^20,x^18) [matched to n=16 (x^12,x^10)] ===", flush=True)
    n = 32; e, f = 20, 18
    prev = None
    for r in [4,5,6]:
        res = measure(n, e, f, r)
        if res is None:
            print(f"  r={r}: SKIP", flush=True); continue
        ratio = (res['nbad']/prev) if (prev not in (None,0)) else None
        rs = f"{ratio:.2f}" if ratio is not None else "-"
        print(f"  r={r} (x^{e},x^{f}): #bad={res['nbad']} O_P={res['OP']} K={res['K']} "
              f"bad/K={res['nbad']/res['K']:.3f}  slide_ratio_from_prev={rs}", flush=True)
        prev = res['nbad']
    print(flush=True)
    print("=== cross-group matched family (x^{n/2+4},x^{n/2+2}), depth r=4 fixed, vary n ===", flush=True)
    print("(tests whether #bad(r,n)/#bad(r,n/2) multiplier is constant or grows)", flush=True)
    prevb = None
    for n in [8,16,32]:
        e = n//2+4; f = n//2+2; r = 4
        if e-r < 0 or f-r < 0 or n < 2*(r+1):
            print(f"  n={n}: SKIP", flush=True); continue
        res = measure(n, e, f, r)
        if res is None:
            print(f"  n={n}: SKIP(neg)", flush=True); continue
        mult = (res['nbad']/prevb) if (prevb not in (None,0)) else None
        ms = f"{mult:.2f}" if mult is not None else "-"
        print(f"  n={n} r=4 (x^{e},x^{f}): #bad={res['nbad']} O_P={res['OP']}  mult_from_n/2={ms}", flush=True)
        prevb = res['nbad']
