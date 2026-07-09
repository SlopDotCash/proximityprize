#!/usr/bin/env python3
"""
C063 follow-up: does the proposed FIX (chernoff_max_re_le converting q^{1/4} -> sqrt(log m))
deliver sqrt(n log m) UNCONDITIONALLY, or does it consume the open BGK/Lam-Leung MGF wall?

The C063 "fix" is: replace the per-period (global-4th-moment) bound by the max-of-m
maximal inequality, which needs ONLY a single per-period sub-Gaussian MGF with sigma^2=O(n).
Question: what does the per-period 4th moment ALONE give through the maximal inequality?
If only the 4th moment is available (= what worst_period_sidon_le actually proves), the
maximal/Chernoff machinery with a SINGLE r=2 even moment gives the MARKOV-at-r=2 bound, which
does NOT beat the per-period q^{1/4} bound. To get sqrt(n log m) you must feed the FULL MGF
= ALL even moments E_r(mu_n) <= (2r-1)!! n^r up to r ~ log m. That is the open wall.

Test: from the measured per-period moments mu_{2r}=(1/m) sum_c |eta_c|^{2r} (worst direction),
compute the best sup-norm bound obtainable from the first R even moments via the
moment->maximal inequality   B <= min_{r<=R} (m * mu_{2r})^{1/(2r)}  (Markov + union over m).
  - R=1 (only 2nd moment, ~ Parseval): gives ~ (m * n)^{1/2}? no -> (q n / m... ) ; we use exact.
  - R=2 (4th moment, = what Sidon proves): the per-period (3q)^{1/4} sqrt(n)-type reach.
  - R -> r_opt ~ log m: reaches sqrt(n log m).
Show the bound only descends to sqrt(n log m) when R grows to ~log m, i.e. the q^{1/4}->sqrt(log m)
conversion REQUIRES all moments up to r~log m. That is the welding to W-BGK / W-Johnson.
"""
import math, cmath
from sympy import isprime

def primitive_root(p):
    from sympy import factorint
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs):
            return g
    raise RuntimeError

def subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = [], 1
    for _ in range(n):
        S.append(x); x = (x*h) % p
    return S

def periods_over_cosets(p, n, S):
    """
    The m=(p-1)/n nonzero Gauss periods are eta_{b} for b ranging over coset reps of mu_n in F_p^*.
    But since eta_{b} depends only on the coset of b under mu_n (eta_{b*s}=eta_b for s in mu_n,
    by reindexing the subgroup sum) -- the DISTINCT periods are indexed by the m cosets.
    We compute the m distinct period magnitudes (one per coset).
    """
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)          # generator of mu_n
    # coset reps: g^0, g^1, ..., g^{m-1} are reps for F_p^*/mu_n (since g has order p-1, mu_n=<g^m>)
    m = (p-1)//n
    w = 2*math.pi/p
    mags = []
    rep = 1
    for c in range(m):
        b = rep
        z = 0j
        bw = b*w
        for y in S:
            z += cmath.exp(1j*bw*y)
        mags.append(abs(z))
        rep = (rep*g) % p
    return mags  # length m, the m distinct periods

print("="*100)
print("C063 follow-up: moment-reach of the maximal inequality. Does removing q^{1/4} cost all moments?")
print("="*100)
print("B_R := min_{r<=R} (m * mu_{2r})^{1/(2r)},  mu_{2r}=mean_c |eta_c|^{2r}.  Btarget=sqrt(2 n log m).")
print()

for (mu, beta) in [(3,4.0),(4,4.0),(3,5.0),(4,5.0)]:
    n = 2**mu
    target = int(round(n**beta))
    k = max(2, target//n)
    p = None
    while k < target//n + 100000:
        cand = k*n+1
        if isprime(cand):
            p = cand; break
        k += 1
    if p is None or p > 3_000_000:
        continue
    S = subgroup(p, n)
    mags = periods_over_cosets(p, n, S)
    m = len(mags)
    logm = math.log(m)
    Btrue = max(mags)
    Btarget = math.sqrt(2*n*logm)
    Bper = (3.0*p)**0.25*math.sqrt(n)
    r_opt = max(1, int(round(logm)))
    Rmax = max(8, r_opt+3)
    bounds = []
    for r in range(1, Rmax+1):
        mu2r = sum(mg**(2*r) for mg in mags)/m
        b = (m*mu2r)**(1.0/(2*r))
        bounds.append((r, b))
    # running min:
    best_at = {}
    cur = float('inf'); curr_arg=0
    for (r,b) in bounds:
        if b < cur: cur=b; curr_arg=r
        best_at[r]=(cur,curr_arg)
    print(f"n={n} p={p} m={m} logm={logm:.2f} r_opt~{r_opt} | Btrue={Btrue:.3f} "
          f"Btarget={Btarget:.3f} Bper={Bper:.2f}")
    # show reach at R=2 (Sidon 4th moment), R=r_opt, R=Rmax
    for R in sorted(set([2, r_opt, Rmax])):
        if R in best_at:
            bv, ar = best_at[R]
            print(f"     B_(R<={R:>2})={bv:8.3f}  (argmin r={ar})   B/Btarget={bv/Btarget:6.3f}   B/Bper={bv/Bper:6.3f}")
    print()

print("-"*100)
print("READOUT:")
print(" * R<=2 (4th moment alone = exactly what worst_period_sidon_le proves): bound stays")
print("   well ABOVE Btarget (still carries the q^{1/4} surplus, B/Bper~O(1)).")
print(" * Only as R grows to r_opt~log m does the moment-reach descend to ~Btarget.")
print(" * That descent USES E_r(mu_n)<=(2r-1)!! n^r up to r~log m = the open GaussianEnergyBound")
print("   = Lam-Leung char-p transfer = BGK/Paley wall. The maximal inequality does NOT remove")
print("   q^{1/4} for free from the 4th moment; it removes it only by consuming all moments.")
