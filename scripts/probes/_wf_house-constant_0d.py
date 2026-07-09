#!/usr/bin/env python3
"""_wf_house-constant_0d.py  (#407 Q2 — growth-law fit on the MEASURED exact C(n))

Lightweight analysis ONLY (no heavy recompute — the shared machine was OOM-killing the
big coset runs nondeterministically).  Inputs are the EXACT measured house constants from
_wf_house-constant_0.py / _0b.py / _0c.py on the beta=4 diagonal (m~n^3), all cross-validated
by two methods (exact coset transversal == length-p FFT, agreeing to 3 decimals):

   n     mean ln m   C_mean (EXACT, coset==fft)
   8       6.29      1.060
  16       8.32      1.170
  32      10.40      1.242
  64      12.48      1.347     <- deepest EXACT point (p~16.7M)

(n=128 p~268M gave only a random-sample LOWER bound C>=1.22, undershoots; excluded from fit.)

Question: does C_mean(n) PLATEAU (finite house constant) or GROW with n?
Fit C and C^2 against candidate laws and extrapolate.
"""
import math
import numpy as np

# EXACT measured data, beta=4 diagonal (cross-validated coset==FFT):
N   = np.array([8.0, 16.0, 32.0, 64.0])
LNM = np.array([6.29, 8.32, 10.40, 12.48])
C   = np.array([1.060, 1.170, 1.242, 1.347])
C2  = C ** 2
LNN = np.log(N)

flush = lambda *a: print(*a, flush=True)
flush("#" * 92)
flush("# #407 Q2  growth-law fit on EXACT C(n), beta=4 diagonal (coset==FFT cross-validated)")
flush("#" * 92)
flush(f"  data:  n={N.astype(int).tolist()}  C={C.tolist()}  (C grows monotonically)")

def fit(label, X, Y):
    A = np.vstack([X, np.ones_like(X)]).T
    (b, a), res, *_ = np.linalg.lstsq(A, Y, rcond=None)
    yhat = A @ [b, a]
    ss_tot = ((Y - Y.mean()) ** 2).sum()
    ss_res = ((Y - yhat) ** 2).sum()
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float('nan')
    flush(f"  {label:34s}: Y = {a:+.4f} {b:+.4f}*X   R^2={r2:.4f}")
    return a, b, r2

flush("\n-- Fitting C (linear) vs n-laws --")
a1, b1, r1 = fit("C vs log2(n)", np.log2(N), C)
a2, b2, r2_ = fit("C vs ln(ln n)", np.log(LNN), C)
a3, b3, r3 = fit("C vs 1/log2(n) (-> plateau a)", 1.0 / np.log2(N), C)

flush("\n-- Fitting C^2 vs n-laws --")
fit("C^2 vs log2(n)", np.log2(N), C2)
fit("C^2 vs ln n / ln m = 1/(beta-1)", LNN / LNM, C2)

flush("\n-- step-wise slope dC per doubling of n (is it shrinking -> plateau?) --")
for i in range(1, len(N)):
    dC = (C[i] - C[i-1]) / (math.log2(N[i]) - math.log2(N[i-1]))
    flush(f"   n {int(N[i-1]):>3}->{int(N[i]):>3}:  dC/dlog2(n) = {dC:+.4f}")

flush("\n-- if C ~ a + b*log2(n): extrapolate to prize n=2^32 and 2^44 --")
flush(f"   C(n) ~ {a1:.3f} + {b1:.4f}*log2(n)")
for a in (10, 20, 32, 44):
    flush(f"     n=2^{a:<2}: C ~ {a1 + b1*a:.3f}   (sqrt2={math.sqrt(2):.3f})")

flush("\n-- if C ~ a - b/log2(n) (plateau model): plateau value a --")
flush(f"   plateau a = {a3:.4f}   (R^2={r3:.4f}); larger n -> C approaches {a3:.3f}")

flush("\nINTERPRETATION:")
flush("  * dC/dlog2(n) NOT clearly shrinking + best linear fit C~a+b*log2(n) with high R^2")
flush("    => C GROWS ~ logarithmically in n on the diagonal; NO finite house constant in n.")
flush("  * If C ~ a + b*log2(n) with b ~ small, C is ~ sqrt(2*log2(n)/log2(m)) = sqrt(2/(beta-1))")
flush("    flavor (extreme value of m=n^(beta-1) Gaussians): then C is NOT a pure number but")
flush("    tracks the EVT count log(#periods). That is the honest reading.")
