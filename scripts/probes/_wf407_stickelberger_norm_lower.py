"""
#407 Stickelberger NORM LOWER-bound test -- the genuinely new direction.

The prior loop showed Stickelberger cannot UPPER-bound the house (the archimedean
max lives in the unit part, valuation-blind).  NEW question: can Stickelberger give
a useful LOWER bound or ANTI-flatness?

Mechanism: by AM-GM, house = max|eta_b| >= geomean = |N|^{1/m}, N = prod eta_b in Z.
Stickelberger pins N exactly (it's the norm = a product of Jacobi-sum-type integers).
IF the digit-sum structure forces |N| to be LARGE (a high power of p), then geomean
is large, forcing house large -- but the prize wants an UPPER bound, so a large
lower bound is the WRONG direction (it would make the prize HARDER, even refute the
target if it exceeded C sqrt(n log m)).

So the real test is two-pronged:
 (A) Does |N|^{1/m} (the Stickelberger-pinned geomean lower bound on house) ever
     EXCEED the target C sqrt(n log m)?  If yes -> Stickelberger REFUTES flatness
     for those params (a real partial result!).  If always below -> consistent,
     no obstruction, Stickelberger lower bound is too weak (loose by house/geomean).
 (B) How does house/geomean (the gap Stickelberger misses) scale with m?  If it is
     ~sqrt(log m) -> exactly the prize factor lives OUTSIDE Stickelberger (refutes
     the route as a closer).  If bounded -> Stickelberger geomean WOULD essentially
     pin the house (route would be viable).
"""
import numpy as np, cmath, math
from sympy import primitive_root
from functools import reduce

def setup(p, n):
    g = primitive_root(p); m = (p-1)//n
    w = cmath.exp(2j*math.pi/p)
    mu_n = [pow(g, m*l, p) for l in range(n)]
    def eta(b): return sum(w**((b*y) % p) for y in mu_n)
    reps = [pow(g, c, p) for c in range(m)]
    return m, eta, reps

rows = []
# sweep many primes with n fixed-ish, growing m, to see the scaling of house/geomean
import sympy
for n in [8, 16]:
    primes = [p for p in sympy.primerange(50, 8000) if (p-1) % n == 0][:14]
    for p in primes:
        m, eta, reps = setup(p, n)
        if m < 2: continue
        conj = np.array([eta(b) for b in reps])
        mags = np.abs(conj)
        house = mags.max(); gmean = np.exp(np.mean(np.log(mags+1e-30)))
        Nabs = abs(reduce(lambda a, b: a*b, conj, 1+0j))
        target = math.sqrt(n*math.log(max(m, 2)))
        rows.append((n, p, m, house, gmean, Nabs**(1/m), house/gmean,
                     house/target, (Nabs**(1/m))/target))

print(f"{'n':>3}{'p':>6}{'m':>5}{'house':>8}{'gmean':>7}{'|N|^1/m':>9}"
      f"{'h/gm':>6}{'h/tgt':>7}{'gm/tgt':>7}")
for r in rows:
    print(f"{r[0]:>3}{r[1]:>6}{r[2]:>5}{r[3]:>8.2f}{r[4]:>7.2f}{r[5]:>9.3f}"
          f"{r[6]:>6.2f}{r[7]:>7.3f}{r[8]:>7.3f}")

# scaling of house/geomean vs sqrt(log m): regression
import numpy as np
arr = np.array(rows, dtype=float)
hg = arr[:, 6]; logm = np.log(arr[:, 2])
# fit hg ~ a*sqrt(log m)
sl = np.sqrt(logm)
coef = np.dot(hg, sl)/np.dot(sl, sl)
print(f"\nhouse/geomean ~ {coef:.3f} * sqrt(log m)  (R: corr={np.corrcoef(hg,sl)[0,1]:.3f})")
print("gm/tgt = Stickelberger geomean LOWER bound as fraction of target sqrt(n log m).")
print("If gm/tgt < 1 always: lower bound never refutes (consistent, but too weak).")
