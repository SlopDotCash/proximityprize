"""
probe_freeprob_spike_atom_444.py  (#444, lens = [free-prob-spike])

LENS HYPOTHESIS
---------------
Model the m = (p-1)/n real Gauss-period values  X_c = eta_c / sqrt(n)  as a
MIXTURE measure on the real line:

    mu_emp  =  (1 - w) * N(0, sigma_bulk^2)   +   w * (1/2)(delta_{+a} + delta_{-a})

i.e. a bulk Gaussian PLUS a symmetric two-point atom at +-a carrying total mass w.
The atom is meant to be the carrier of the EXTREME values (the "house"
M(n) = max_c |eta_c| = sqrt(n) * max_c |X_c|), so a := house/sqrt(n) and the
extreme is reached when at least ONE of the m draws lands in the atom:
    w * m  ~  1   (the atom is a single-coset event in expectation).

The classical EVT crown died because it modeled the bulk only and got
max ~ sqrt(2 log m) (Gaussian EVT, constant -> sqrt2).  The spike lens instead
PINS the extreme by the atom location a, and reads the atom MASS w off the
LOW even moments of the EMPIRICAL period distribution -- which are KNOWN in
closed form (in-tree Bessel / Duke-Garcia):

    E2 := E[X^2]     = 1            (Parseval, exact, all n)
    E4 := E[X^4]     = 3 - 3/n      (Duke-Garcia / kappa4 = -3/n)
    E6 := E[X^6]     = 15 - 30/n + (in-tree)   (15*(1 - 3/(2n) + ...) approx)

MIXTURE MOMENT EQUATIONS (symmetric, bulk var = s2, atom at +-a, mass w):
    m2 = (1-w) s2          +  w a^2                 = 1
    m4 = (1-w) 3 s2^2      +  w a^4                 = 3 - 3/n
    m6 = (1-w) 15 s2^3     +  w a^6                 = 15 - 45/n + ...   (probe-measured)

THE CIRCULARITY TEST (the honest check the lens demands)
--------------------------------------------------------
The lens is only NON-trivial if we can solve for (w, a, s2) from KNOWN closed
moments WITHOUT already knowing a = house/sqrt(n).  We have 3 unknowns.
Two natural closures:

  (C-known-a)  PIN a from the conjectured house a = C*sqrt(log m)  (C=O(1)).
               Then (w, s2) solve from m2, m4.  ==> w is a CLOSED function of
               (n, m).  BUT this INPUTS the house -> CIRCULAR.

  (C-moments)  Use THREE known moments m2, m4, m6 -> solve all of (w, a, s2)
               from moments ALONE.  Then OUTPUT a, and house = a*sqrt(n).
               This is NON-circular IFF the moment system has a real solution
               with a -> infinity (or a -> sqrt(log m)) as n,m grow.

This probe runs BOTH closures on real Gauss periods and asks:
  (1) Does (C-moments) yield a real, sensible atom (0<w<1, a>s)?
  (2) Does the moment-derived a track sqrt(log m) (the house) or stay O(1)?
  (3) -> verdict on which horn the lens falls on.
"""

import numpy as np
from sympy import primerange

def gauss_periods(p, n):
    """Real Gauss periods eta_c = sum_{x in mu_n} cos(2 pi b x / p), one per coset.
    Returns the m=(p-1)/n period values."""
    # primitive root g of F_p
    def primitive_root(p):
        from sympy import factorint
        fs = list(factorint(p-1).keys())
        for g in range(2, p):
            if all(pow(g, (p-1)//q, p) != 1 for q in fs):
                return g
        raise RuntimeError
    g = primitive_root(p)
    m = (p-1)//n
    # mu_n = { g^(m*j) : j } ; coset reps b_c = g^c, c=0..m-1
    h = pow(g, m, p)                      # generator of mu_n
    mu = [1]
    for _ in range(n-1):
        mu.append((mu[-1]*h) % p)
    mu = np.array(mu, dtype=np.int64)
    periods = np.empty(m)
    gc = 1
    two_pi_over_p = 2*np.pi/p
    for c in range(m):
        # eta for b = g^c : sum cos(2 pi (b * x)/p), x in mu_n
        bx = (gc * mu) % p
        periods[c] = np.cos(two_pi_over_p * bx).sum()
        gc = (gc*g) % p
    return periods   # length m, real

def solve_moments_closure(m2, m4, m6):
    """Solve symmetric 2-point + Gaussian-bulk mixture from 3 moments.
    Unknowns: w in (0,1), a>0, s2>0.
      m2 = (1-w) s2      + w a^2
      m4 = 3(1-w) s2^2   + w a^4
      m6 = 15(1-w) s2^3  + w a^6
    Numerically solve. Returns (w, a, s2) or None."""
    from scipy.optimize import brentq
    # parameterize by s2; for given s2 the two linear-ish eqs in (w, w a^2,...) :
    # let A = a^2. unknowns w, A. From m2,m4:
    #   w(A - s2) = m2 - s2
    #   w(A^2 - 3 s2^2) = m4 - 3 s2^2
    # => (m2-s2)*(A + s2)*?  ... solve A from ratio then w, then check m6.
    def residual_m6(s2):
        # from m2: w(A - s2) = m2 - s2          (E1)
        # from m4: w(A^2 - 3 s2^2) = m4 - 3 s2^2 (E2)
        # divide: (A^2 - 3 s2^2)/(A - s2) = (m4 - 3 s2^2)/(m2 - s2) =: R
        num = m2 - s2
        if abs(num) < 1e-15:
            return None
        R = (m4 - 3*s2**2)/num
        # (A^2 - 3 s2^2) = R (A - s2)  => A^2 - R A + (R s2 - 3 s2^2) = 0
        disc = R*R - 4*(R*s2 - 3*s2**2)
        if disc < 0:
            return None
        A = (R + np.sqrt(disc))/2     # take larger root => atom OUTSIDE bulk
        if A <= s2:
            return None
        w = (m2 - s2)/(A - s2)
        if not (0 < w < 1):
            return None
        a = np.sqrt(A)
        m6_pred = 15*(1-w)*s2**3 + w*a**6
        return m6_pred - m6, w, a, s2
    # scan s2 in (0, m2) for sign change of m6 residual
    s2_grid = np.linspace(1e-4, m2*0.999, 4000)
    prev = None
    for s2 in s2_grid:
        r = residual_m6(s2)
        if r is None:
            prev = None
            continue
        val = r[0]
        if prev is not None and prev[0]*val < 0:
            # bisect
            lo, hi = prev[1], s2
            for _ in range(60):
                mid = (lo+hi)/2
                rm = residual_m6(mid)
                if rm is None:
                    break
                if rm[0]*residual_m6(lo)[0] < 0:
                    hi = mid
                else:
                    lo = mid
            rr = residual_m6((lo+hi)/2)
            if rr is not None:
                return rr[1], rr[2], rr[3]
        prev = (val, s2)
    return None

print(f"{'p':>8} {'n':>4} {'m':>6} {'house/sqn':>10} {'sqrt(logm)':>10} "
      f"{'m4':>7} {'m6':>8} | {'w_mom':>9} {'a_mom':>8} {'s_mom':>7} {'a/sqrtlogm':>10}")
print("-"*120)

# prize-shaped diagonal: keep n a power of 2, p ~ n^beta, THIN, proper subgroup,
# exclude Fermat (fully dyadic) primes.
configs = []
for n in [16, 32, 64, 128]:
    # find primes p = 1 mod n with p ~ n^4..n^5, odd_part((p-1)/n) > 1
    target = int(n**4.3)
    found = 0
    for p in primerange(target, target*6):
        if (p-1) % n == 0:
            m = (p-1)//n
            # require proper (m>1) and not fully dyadic (odd part of m > 1)
            op = m
            while op % 2 == 0:
                op //= 2
            if m > 4 and op > 1:
                configs.append((p, n))
                found += 1
                if found >= 1:
                    break

for p, n in configs:
    per = gauss_periods(p, n)
    m = len(per)
    X = per/np.sqrt(n)
    m2 = np.mean(X**2)
    m4 = np.mean(X**4)
    m6 = np.mean(X**6)
    house = np.max(np.abs(per))
    sol = solve_moments_closure(m2, m4, m6)
    if sol is None:
        wm, am, sm = float('nan'), float('nan'), float('nan')
    else:
        wm, am, sm = sol
    sqrtlogm = np.sqrt(np.log(m))
    ratio = am/sqrtlogm if sol else float('nan')
    print(f"{p:>8} {n:>4} {m:>6} {house/np.sqrt(n):>10.3f} {sqrtlogm:>10.3f} "
          f"{m4:>7.3f} {m6:>8.3f} | {wm:>9.5f} {am:>8.3f} {sm:>7.4f} {ratio:>10.3f}")

print()
print("HORN TEST:")
print(" - If a_mom (moment-derived atom location) tracks house/sqrt(n) ~ sqrt(log m),")
print("   the lens is NON-circular and DERIVES the house from closed low moments.")
print(" - If a_mom stays O(1) (~ a few * the bulk std) while the TRUE house/sqrt(n)")
print("   grows like sqrt(log m), the low-moment atom is a BULK feature, NOT the")
print("   extreme -> the spike cannot see the house from finitely many moments")
print("   (the house lives in moment r ~ log m, the deep-moment wall). CIRCULAR/dead.")
