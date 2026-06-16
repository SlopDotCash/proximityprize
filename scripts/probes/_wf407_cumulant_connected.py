#!/usr/bin/env python3
"""
#407 ROUTE [cumulant] — does the CONNECTED (classical) cumulant expansion of X=|eta_b|^2 have
signed cancellation that the RAW moment misses, pushing effective moment depth past the r=2 Betti
wall (CharSumMomentDeepWall)?

SETUP. b uniform over F_p^*; X_b = |eta_b|^2, eta_b = sum_{x in mu_n} e_p(b x). The PRIZE FLOOR is
B = max_b |eta_b| = sqrt(max_b X_b). The moment method bounds B via the raw 2r-th moment
  M_{2r} := sum_{b!=0} |eta_b|^{2r} = p*E_r - n^{2r},     E_r = char-p additive energy of mu_n.
Wall: E_r is at its char-0 value (2r-1)!! n^r ONLY for r <= r_max ~ 2 log_n p; past that the mod-q
DEFECT (E_r^{Fq} - E_r^{C}) overtakes and M_{2r} blows up, capping the provable depth at r_max
(=2 in the prize regime m=2^128, p~n*2^128 -> log_n p ~ 1 asymptotically).

THIS PROBE. Compute the CLASSICAL CUMULANTS kappa_r of X (from the log-MGF: log E[e^{tX}] =
sum_r kappa_r t^r / r!). Cumulants are SIGNED partition-Mobius combinations of the moments. The
hope (my route): the connected cumulant kappa_r is much smaller than the raw moment mu_r because
the disconnected (Gaussian/diagonal) mass cancels in the signed expansion, so a cumulant-based
transport could reach deeper r. TEST whether kappa_r's mod-q defect is suppressed relative to
mu_r's defect. EXACT integer/rational arithmetic (sympy) for small dyadic primes.

Reports, per (n, p):
  - mu_r (raw moment of X, scaled by Gaussian baseline of the moment)
  - kappa_r (connected cumulant) and its standardized size kappa_r / kappa_2^{r/?}
  - DEFECT decomposition of BOTH mu_r and kappa_r: char-0 (archimedean) vs mod-q part
  - the key ratio: does |kappa_r^{defect}| / |mu_r^{defect}| -> 0 (cancellation) or O(1) (no help)?
"""
import math, itertools, cmath
from fractions import Fraction
from collections import defaultdict

# ---------- number theory ----------
def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0: return m == p
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_1_mod_n_near(target, n):
    p = target - (target % n) + 1
    if p > target: p -= n
    while p > n:
        if is_prime(p): return p
        p -= n
    return None

def order_n_gen(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s = set(); x = 1
        for _ in range(n): s.add(x); x = x*h % p
        if len(s) == n: return h
    return None

def dfac2(r):  # (2r-1)!!
    x = 1
    for i in range(1, r+1): x *= (2*i-1)
    return x

# ---------- the F_p energies E_r = (1/p) sum_b |S(b)|^{2r}  (EXACT integer) ----------
def Er_Fq_exact(p, n, h, rmax):
    """EXACT integer additive energies E_r(mu_n) in F_p, r=1..rmax, via the convolution
       count of r-fold subset sums. E_r = sum_v R_r(v)^2, R_r(v)=#{x in mu_n^r : sum x = v mod p}."""
    mu = [pow(h, i, p) for i in range(n)]
    # R_1
    R = [0]*p
    for x in mu: R[x] += 1
    Es = {}
    cur = R[:]            # R_r as we go
    for r in range(1, rmax+1):
        Es[r] = sum(c*c for c in cur)   # exact integer energy
        if r < rmax:
            nxt = [0]*p
            for v in range(p):
                cv = cur[v]
                if cv:
                    for x in mu:
                        nxt[(v + x) % p] += cv
            cur = nxt
    return Es   # exact integers

# ---------- char-0 energies (exact, brute, integer) ----------
def Er_char0_exact(n, rmax):
    angles = [2*math.pi*i/n for i in range(n)]
    pts = [cmath.exp(1j*a) for a in angles]
    res = {}
    for r in range(1, rmax+1):
        if n**r > 3_000_000:
            res[r] = None; continue
        cnt = defaultdict(int)
        for combo in itertools.product(range(n), repeat=r):
            s = sum(pts[i] for i in combo)
            key = (round(s.real, 6), round(s.imag, 6))
            cnt[key] += 1
        res[r] = sum(v*v for v in cnt.values())
    return res

# ---------- moments and cumulants of X = |eta_b|^2 over b != 0 ----------
# mu_r = E[X^r] = (1/(p-1)) sum_{b!=0} |eta_b|^{2r} = (p E_r - n^{2r})/(p-1)   (EXACT Fraction)
def raw_moments_from_energy(Es, p, n, rmax):
    mu = {}
    for r in range(1, rmax+1):
        if Es.get(r) is None: mu[r] = None; continue
        mu[r] = Fraction(p*Es[r] - n**(2*r), p-1)
    return mu

def moments_to_cumulants(mu, rmax):
    """Classical cumulants from raw moments via the recursion
       kappa_n = mu_n - sum_{k=1}^{n-1} C(n-1,k-1) kappa_k mu_{n-k}.  EXACT Fraction."""
    from math import comb
    kap = {}
    for n_ in range(1, rmax+1):
        if mu.get(n_) is None: kap[n_] = None; continue
        s = mu[n_]
        ok = True
        for k in range(1, n_):
            if kap.get(k) is None or mu.get(n_-k) is None: ok = False; break
            s -= comb(n_-1, k-1) * kap[k] * mu[n_-k]
        kap[n_] = s if ok else None
    return kap

# ---------- main ----------
print("="*112)
print("ROUTE [cumulant]: connected cumulants kappa_r of X=|eta_b|^2 vs raw moments mu_r — does the")
print("signed expansion cancel the mod-q DEFECT and beat the r=2 Betti wall?  (EXACT arithmetic)")
print("="*112)

for n in (4, 8, 16):
    rmax = 7 if n == 4 else (6 if n == 8 else 4)
    Ec = Er_char0_exact(n, rmax)
    print(f"\n{'#'*100}\nn = {n}")
    for beta in (2.0, 3.0, 4.0, 5.0):
        p = prime_1_mod_n_near(int(n**beta), n)
        if p is None or p > 1_500_000: continue
        h = order_n_gen(p, n)
        if h is None: continue
        Efq = Er_Fq_exact(p, n, h, rmax)
        mu  = raw_moments_from_energy(Efq, p, n, rmax)
        kap = moments_to_cumulants(mu, rmax)
        # char-0 reference moments/cumulants (the clean baseline)
        muC = {r: (Fraction(p*Ec[r] - n**(2*r), p-1) if Ec.get(r) is not None else None)
               for r in range(1, rmax+1)}
        kapC = moments_to_cumulants(muC, rmax)
        bdig = round(math.log(p)/math.log(n), 2)
        print(f"\n  p = {p}  (n^{beta}, log_n p = {bdig});  E_r^Fq vs E_r^C:")
        # standardized cumulant: kappa_r / kappa_2^{r-1} type — but better compare DEFECT in cumulant
        print(f"    {'r':>2} | {'mu_r/baseline':>14} | {'kappa_r':>16} | "
              f"{'mu_r DEFECT':>14} | {'kap_r DEFECT':>14} | {'|kapD|/|muD|':>11}")
        base2 = None
        for r in range(1, rmax+1):
            if mu.get(r) is None: continue
            baseline = dfac2(r) * n**r * Fraction(p, p-1)   # E[X^r] Gaussian baseline ~ (2r-1)!! n^r
            muD = (mu[r] - muC[r]) if muC.get(r) is not None else None
            kapD = (kap[r] - kapC[r]) if (kap.get(r) is not None and kapC.get(r) is not None) else None
            ratio = (abs(float(kapD))/abs(float(muD))) if (muD not in (None,) and muD != 0 and kapD is not None) else float('nan')
            mu_sc = float(mu[r]/baseline) if baseline != 0 else float('nan')
            kr = float(kap[r])
            muD_s = float(muD) if muD is not None else float('nan')
            kapD_s = float(kapD) if kapD is not None else float('nan')
            print(f"    {r:>2} | {mu_sc:>14.4f} | {kr:>16.4e} | "
                  f"{muD_s:>14.4e} | {kapD_s:>14.4e} | {ratio:>11.4f}")
print("""
READ:
- mu_r/baseline > 1 and growing == the raw-moment defect (the wall). mu_r DEFECT = mod-q excess.
- kap_r DEFECT = the same mod-q excess as seen by the CONNECTED cumulant.
- |kapD|/|muD|: if -> 0 as r grows, the signed cumulant expansion CANCELS the defect (route wins).
  If O(1) or growing, the cumulant inherits the defect at the SAME order (route gives no new depth).
""")
