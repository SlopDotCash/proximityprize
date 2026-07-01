"""
probe_444_angleD_windowshift.py  (#444 Angle D -- the h-window SHIFT recursion, SAME group)

The bad test at depth r on line (x^e,x^f) uses the 2x2 Hankel/Jacobi-Trudi window
   M_r(S) = [[h_{e-r}, h_{e-r+1}],[h_{f-r}, h_{f-r+1}]],  det M_r = 0.
At depth r-1 (a0=r, deficit still 2) on the SAME line the window is
   M_{r-1}(S') = [[h_{e-r+1}, h_{e-r+2}],[h_{f-r+1}, h_{f-r+2}]]
i.e. the window SLIDES UP by one in degree. So depth-r and depth-(r-1) are CONSECUTIVE 2x2
minors of the SAME infinite Hankel-like matrix of h_m's (rows = e-shift, f-shift). This is the
generating-function recursion: bad-at-r and bad-at-(r-1) are governed by adjacent minors.

We probe: do the depth-r bad subsets (|S|=r+1) and depth-(r-1) bad subsets (|S|=r) on the SAME
line relate?  They live on different-size subsets, so direct equality is impossible. Instead we
test the GENERATING-FUNCTION / three-term Hankel identity:
  For a Hankel matrix H_{ij}=h_{i+j}, consecutive 2x2 minors satisfy det relations. But our window
  is NOT pure Hankel (two independent row-shifts e,f). We test numerically whether the SET of
  gammas at depth r is contained in / related to the set at depth r-1 (same line), and whether
  #bad(r) <= C(n,r+1)/C(n,r) * #bad(r-1) type slide bounds hold.

Also: the REAL induction target. Instead of maximizer lines, bound #bad(r,n) <= K for EVERY line
by a slide.  We tabulate, for a FIXED line, #bad at depths r-1, r, r+1 and the ratios.
"""
import itertools, sys
from math import comb, gcd
from collections import Counter
sys.path.insert(0, "C:/Users/Administrator/arklib/scripts/probes")
from probe_444_angleD_recursion import measure, w_of_order, P

def scan_depths_fixed_line(n, e, f, rmin, rmax):
    """For a fixed (e,f) line, report #bad and O_P at each depth r in [rmin,rmax]."""
    out = {}
    for r in range(rmin, rmax+1):
        res = measure(n, e, f, r)
        if res is None: continue
        out[r] = res
    return out

if __name__ == "__main__":
    print("=== SAME-LINE depth scan: #bad(r) and O_P(r) for fixed (e,f), n=16 ===", flush=True)
    # pick a few representative lines and slide r
    lines16 = [(8,7),(10,5),(9,15),(12,10),(11,3),(8,3)]
    for (e,f) in lines16:
        n = 16
        ds = scan_depths_fixed_line(n, e, f, 3, 6)
        s = []
        for r in sorted(ds):
            res = ds[r]
            s.append(f"r{r}:#bad={res['nbad']},OP={res['OP']},K={res['K']},bad/K={res['nbad']/res['K']:.3f}")
        print(f"line(x^{e},x^{f}) d={gcd((e-f)%n,n)}: " + " | ".join(s), flush=True)
    print()
    print("=== SAME-LINE slide ratios #bad(r+1)/#bad(r) (does it stay bounded by ~2?) ===", flush=True)
    for (e,f) in lines16:
        n=16
        ds = scan_depths_fixed_line(n, e, f, 3, 6)
        rs = sorted(ds)
        ratios=[]
        for i in range(1,len(rs)):
            a=ds[rs[i-1]]['nbad']; b=ds[rs[i]]['nbad']
            ratios.append(f"{rs[i-1]}->{rs[i]}:{(b/a if a else float('inf')):.2f}")
        print(f"line(x^{e},x^{f}): " + " ".join(ratios), flush=True)
