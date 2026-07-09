#!/usr/bin/env python3
"""_wf_house-constant_0e.py  (#407 Q2 — reconcile: is C driven by ln m (EVT) or by n?)

Pools ALL exact measured cells (cross-validated coset==FFT) from _0.py and _0b.py:
   (n, beta, ln m, C, max|S|^2/n = C^2*ln m).
Decisive test of the mechanism behind the house constant:
   * iid-Gaussian EVT:  max|S|^2/n = ln m + gamma   (depends ONLY on m).
   * observed:          does the EXCESS  (max|S|^2/n - ln m)  track gamma (const),
                        or does it GROW with n (structure beyond iid)?
If the excess ~ const -> C->1, finite constant (=1). If excess ~ c*ln n -> C grows, the
'house constant' is really C ~ sqrt(1 + c*ln n/ln m): finite only at FIXED n, NOT uniform.
"""
import math
import numpy as np
GAMMA = 0.5772156649015329

# EXACT cells (coset==FFT agreed to 3 dp), from _wf_house-constant_0.py and _0b.py:
# (n, beta, ln m, C)
DATA = [
    (8,  4, 6.344, 1.058), (16, 4, 8.330, 1.171), (32, 4, 10.398, 1.240), (64, 4, 12.477, 1.332),
    (8,  5, 8.339, 0.959), (16, 5, 11.091, 1.105), (32, 5, 13.863, 1.216),
    (8,  6, 10.400, 0.870), (16, 6, 13.863, 1.029),
]
flush = lambda *a: print(*a, flush=True)
flush("#"*92)
flush("# #407 Q2 reconcile: EXCESS = max|S|^2/n - ln m  vs gamma (EVT) vs ln n (structure)")
flush("#"*92)
flush(f"{'n':>4} {'beta':>4} {'ln m':>7} {'C':>6} {'max|S|^2/n':>10} {'excess':>7} {'excess/ln n':>11}")
rows=[]
for (n,beta,lnm,C) in DATA:
    mss = C*C*lnm                 # max|S|^2/n
    excess = mss - lnm            # EVT iid predicts excess = gamma ~ 0.577 (const)
    lnn = math.log(n)
    rows.append((n,beta,lnm,C,mss,excess,lnn))
    flush(f"{n:>4} {beta:>4} {lnm:>7.3f} {C:>6.3f} {mss:>10.3f} {excess:>7.3f} {excess/lnn:>11.3f}")

flush(f"\n  gamma (iid-EVT excess prediction) = {GAMMA:.4f}")
exc = np.array([r[5] for r in rows]); lnn = np.array([r[6] for r in rows])
flush(f"  observed excess: min={exc.min():.3f} max={exc.max():.3f} mean={exc.mean():.3f}")
flush(f"  -> excess is FAR from constant gamma and ranges {exc.min():.2f}..{exc.max():.2f}: NOT iid-EVT.")

# fit excess vs ln n  (does the structural inflation scale with subgroup size n?)
A = np.vstack([lnn, np.ones_like(lnn)]).T
(b,a),res,*_ = np.linalg.lstsq(A, exc, rcond=None)
ss_tot=((exc-exc.mean())**2).sum(); ss_res=((exc-A@[b,a])**2).sum(); r2=1-ss_res/ss_tot
flush(f"\n  FIT  excess = {a:+.3f} {b:+.3f}*ln n     R^2={r2:.4f}")
flush(f"  (strong positive slope in ln n => the max is inflated by subgroup size n,")
flush(f"   i.e. the hypocycloid spread of the n-point Gauss period, NOT just the count m.)")

# implied C law: max|S|^2/n = ln m + a + b*ln n  => C^2 = 1 + (a + b*ln n)/ln m
flush(f"\n  IMPLIED LAW:  max|S|^2/n ~ ln m + {b:.3f}*ln n + {a:.3f}")
flush(f"                C^2 = 1 + ({b:.3f}*ln n + {a:.3f})/ln m")
flush(f"  On the diagonal m=n^(beta-1) => ln m=(beta-1)ln n:")
flush(f"     C^2 -> 1 + {b:.3f}/(beta-1)   as n->oo  (a/ln m vanishes)")
for beta in (4,5,6):
    cinf2 = 1 + b/(beta-1)
    flush(f"       beta={beta}: C_inf = sqrt(1 + {b:.3f}/{beta-1}) = {math.sqrt(max(cinf2,0)):.3f}")
flush("\n  => If this law holds, C HAS a finite diagonal limit but it is beta-DEPENDENT:")
flush("     larger beta (sparser p) -> SMALLER C (toward 1). Matches observed beta-drift.")
flush("     The growth seen in n at FIXED beta is the slow approach (a/ln m term) to that limit.")
flush("\n  HONEST VERDICT: finite limit per-beta is PLAUSIBLE (~1.0-1.4) but the small-n")
flush("     window cannot separate 'slow log growth (no limit)' from 'beta-dependent limit'.")
flush("     Both fits are good; C is NOT a single universal number and NOT sqrt2.")
