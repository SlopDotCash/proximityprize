"""Build the n=16 maximizer/O_P table across r=3..6 and compare to candidate closed forms."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from math import comb
import probe_444_r6_fast as M

def maximizer(n, r):
    w = M.w_of_order(n); mu = np.array([pow(w, i, M.P) for i in range(n)], dtype=np.int64)
    res = []
    for e in range(1, n):
        for f in range(0, e):
            st = M.census_line(n, r, e, f, mu, w); res.append(((e, f), st))
    res.sort(key=lambda kv: (kv[1]['nbad'], kv[1]['OP']), reverse=True)
    return res[0]

if __name__ == "__main__":
    print("n=16 maximizer table:")
    print(f"{'r':>2} {'maximizer':>12} {'gap':>3} {'#bad':>6} {'O_P':>5} "
          f"{'C(n/4,r-1)':>10} {'C(n/2,r-1)':>10} {'C(n/4,2)':>8}")
    for r in [3, 4, 5, 6]:
        n = 16
        (e, f), st = maximizer(n, r)
        print(f"{r:>2} {('(x^%d,x^%d)'%(e,f)):>12} {e-f:>3} {st['nbad']:>6} {st['OP']:>5} "
              f"{comb(n//4,r-1):>10} {comb(n//2,r-1):>10} {comb(n//4,2):>8}")
