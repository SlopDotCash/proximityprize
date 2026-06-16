# -*- coding: utf-8 -*-
"""
C070 attack: "Azuma sqrt(2 ln m) inflation = additive-vs-multiplicative gap;
replace the additive level-sum cocycle by the multiplicative Jacobi-sum cocycle
(Hasse-Davenport tower) with NO bulk-vs-tail loss."

CLAIM under test (from C070.json attack_plan):
  The tangent sum T(phi) = (1/m) sum_{i<m} J(chi^i, phi), an AVERAGE of m Jacobi
  sums, carries a MULTIPLICATIVE cocycle (Hasse-Davenport: J = -g(chi)g(phi)/g(chi*phi);
  lifting F_q -> F_{q^t} multiplies Gauss sums). The bet: the tower descent on T
  MULTIPLIES Jacobi sums instead of SUMMING periods, so each factor is uniformly
  |.|=sqrt(q)-controlled by Weil -> no L-infty-vs-L^2 (sqrt(2 ln m)) penalty.

  Operative testable sub-claims:
   (Q1) Does the Hasse-Davenport lift give a BOUNDED per-level multiplier on |T(phi)|
        as F_q -> F_{q^2}?  (i.e. is T multiplicative/cocyclic across the lift?)
   (Q2) Is the relevant cancellation actually carried by an average of Jacobi sums in a
        way the multiplicative cocycle controls -- i.e. does an individual |J|=sqrt(q)
        bound + cocycle yield sqrt(n) cancellation for the AVERAGE T, with no ln m loss?

PRIZE REGIME: dyadic mu_n, n=2^mu a PROPER subgroup of F_q*, q prime ~ n^beta, beta~3-5,
n << sqrt(q), large prime, multiple proper subgroups.  Exact integer / high-precision.
"""

import cmath, math
from itertools import product

# ---------- finite field utilities ----------

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    # find a generator of F_p^*
    if p == 2: return 1
    factors = []
    phi = p-1
    n = phi
    d = 2
    while d*d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0: n//=d
        d += 1
    if n > 1: factors.append(n)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in factors):
            return g
    raise RuntimeError

def find_prime(n, beta_target, lo_mult=1):
    """smallest prime p ~ n^beta_target with n | p-1, p prime."""
    target = int(round(n ** beta_target))
    # search p = 1 + n*k near target
    k0 = max(2, target // n)
    for k in range(k0, k0 + 200000):
        p = 1 + n*k
        if is_prime(p):
            # require n proper subgroup (m=(p-1)/n>1) and n<sqrt(p)
            m = (p-1)//n
            if m > 1 and n*n < p:
                return p
    return None

# ---------- characters on F_p ----------

def char_table(p, g, ord_div):
    """multiplicative character chi of order = (p-1)/? ; we build by discrete log.
       Returns dlog table: dlog[x] = k with x = g^k, for x in 1..p-1.
       A character of order d sends x -> exp(2pi i * (a * dlog[x]) / (p-1)) restricted...
       We'll parametrize chars by exponent j in Z/(p-1): chi_j(g^k)=exp(2pi i j k/(p-1)).
    """
    dlog = [0]*(p)
    cur = 1
    for k in range(p-1):
        dlog[cur] = k
        cur = (cur*g) % p
    return dlog

def chi_apply(j, x, p, dlog, pm1):
    # chi_j(x) = exp(2 pi i j dlog[x]/(p-1)), chi_j(0)=0
    if x % p == 0: return 0j
    return cmath.exp(2j*math.pi*(j*dlog[x % p])/pm1)

# ---------- the prize objects over F_p ----------

def subgroup_mu_n(p, g, n):
    """mu_n = order-n subgroup of F_p^* = <g^{(p-1)/n}>."""
    h = pow(g, (p-1)//n, p)
    S = []
    cur = 1
    for _ in range(n):
        S.append(cur)
        cur = (cur*h) % p
    return S  # length n, contains 1

def tangent_sum_T(h_exp, p, g, dlog, pm1, mu_n, chi_order):
    """T_h = sum_{w in mu_n, w!=1} chi^h(1-w)  (the multiplicative tangent sum;
       w=1 excluded since 1-w=0).  chi is the order-m character; here we use chi^h
       meaning the character with exponent h*(p-1)/m? Actually in the tangent-file
       convention, phi is an arbitrary character; we use phi = character of exponent 'phi_exp'.
       To match TangentSumJacobiAverage: T(phi)=sum_{w in ker chi} phi(1-w).
       ker chi = mu_n. phi here = chi^h in the autocorrelation; we treat phi as a free char.
    """
    s = 0j
    for w in mu_n:
        if (1-w) % p == 0:
            continue
        s += chi_apply(h_exp, 1-w, p, dlog, pm1)
    return s

def house_B(p, g, n, mu_n):
    """B = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x)."""
    best = 0.0
    # eta is coset-constant; iterate b over coset reps = g^0..g^{m-1}? simpler: all b, but dedup by value.
    # To stay fast, iterate b=1..p-1 but only m distinct values; we just take max over all b.
    seen = {}
    for b in range(1, p):
        s = 0j
        for x in mu_n:
            s += cmath.exp(2j*math.pi*((b*x) % p)/p)
        v = abs(s)
        if v > best: best = v
    return best

# ---------- main probe ----------

def run_config(n, beta, verbose=True):
    p = find_prime(n, beta)
    if p is None:
        print(f"  [n={n}] no prime found near beta={beta}")
        return None
    g = primitive_root(p)
    pm1 = p-1
    m = pm1 // n
    dlog = char_table(p, g, None)
    mu_n = subgroup_mu_n(p, g, n)

    # tangent sums T_h for h = 1..m-1 (the nontrivial autocorrelation lags).
    # In the autocorr identity, the relevant chars phi=chi^h have order dividing m.
    # We sample phi over the m characters of <chi> (trivial on mu_n): exponent = h*(p-1)/m = h*n.
    Ts = []
    for h in range(1, m):
        phi_exp = (h * n) % pm1   # character of order dividing m, trivial on mu_n's complement struct
        T = tangent_sum_T(phi_exp, p, g, dlog, pm1, mu_n, m)
        Ts.append(abs(T))
    maxT = max(Ts) if Ts else 0.0
    avgT = (sum(t*t for t in Ts)/len(Ts))**0.5 if Ts else 0.0  # L2 rms
    sqrtn = math.sqrt(n)
    L = math.log(m)

    res = dict(n=n, p=p, beta=math.log(p)/math.log(n), m=m,
               maxT=maxT, rmsT=avgT, sqrtn=sqrtn, lnm=L,
               maxT_over_sqrtn=maxT/sqrtn,
               rmsT_over_sqrtn=avgT/sqrtn,
               maxT_over_sqrt_n_lnm=maxT/math.sqrt(n*L) if L>0 else float('nan'))
    if verbose:
        print(f"  n={n:4d} p={p:8d} beta={res['beta']:.2f} m={m:6d}  "
              f"maxT/sqn={res['maxT_over_sqrtn']:.3f}  rmsT/sqn={res['rmsT_over_sqrtn']:.3f}  "
              f"maxT/sqrt(n lnm)={res['maxT_over_sqrt_n_lnm']:.3f}")
    return res, p, g, mu_n, dlog, pm1, m


print("="*78)
print("Q-A: does the tangent sum T_h have the SAME sqrt(ln m) extreme-value scatter")
print("     as the additive house?  (If yes, the 'multiplicative reframing' has the")
print("     SAME L-infty-vs-L^2 gap -- the Azuma loss is NOT an artifact of additivity.)")
print("="*78)
configs = [(8,3.0),(16,3.0),(32,2.7),(64,2.5),(16,3.5),(32,3.0)]
rows = []
for n,beta in configs:
    out = run_config(n,beta)
    if out: rows.append(out[0])

print()
print("  Reading: rmsT/sqrt(n) ~ 1 = generic L^2 cancellation (sqrt(n)).")
print("           maxT/sqrt(n) GROWING with m = L-infty extreme value > L^2 bulk.")
print("           If maxT/rmsT ~ sqrt(ln m), the multiplicative T_h has the SAME")
print("           bulk-vs-tail gap the Azuma route paid -- NO loss-free cocycle.")
print()
for r in rows:
    ratio = r['maxT']/r['rmsT'] if r['rmsT']>0 else float('nan')
    print(f"  n={r['n']:4d} m={r['m']:6d}  maxT/rmsT={ratio:.3f}  sqrt(ln m)={math.sqrt(r['lnm']):.3f}  "
          f"sqrt(2 ln m)={math.sqrt(2*r['lnm']):.3f}")
