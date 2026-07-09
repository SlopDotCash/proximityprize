#!/usr/bin/env python3
"""
C063 probe: Sidon-at-r=2 per-period bound (3q)^{1/4} sqrt(n) vs the target
extreme-value scale sqrt(n log m), m=(p-1)/n.

Claim to test (C063):
  (A) ARITHMETIC GAP IDENTITY: the ratio of the proven per-period bound
      Bper = (3q)^{1/4} sqrt(n) to the target Btarget = sqrt(2 n log m)
      equals exactly  (3q)^{1/4} / sqrt(2 log m)  ~  q^{1/4}/sqrt(log m).
      (This is trivially true by algebra; we just confirm numerically and
       confirm it GROWS like q^{1/4}, i.e. the per-period bound is loose.)
  (B) MEASURED max_b ||eta_b|| is sqrt(n log m)-SCALE, NOT q^{1/4} sqrt(n)-SCALE.
      i.e. Btrue / sqrt(n log m) is BOUNDED O(1), while
           Btrue / ((3q)^{1/4} sqrt(n)) -> 0 like q^{-1/4}.
      This is the substance: the q^{1/4} in the per-period bound is genuine
      SLACK; the truth lives at the extreme-value scale. So the "q^{1/4}
      surplus = extreme-value deficit" reading is numerically supported.

Prize regime: dyadic mu_n, n=2^mu a PROPER subgroup of F_q*, q prime = 1 mod n,
q ~ n^beta, beta ~ 4-5, n << sqrt q. (NEVER the full group.)

Exact integer arithmetic for the subgroup + mod-p; complex exp in double for
the period magnitudes (this is unavoidable and standard, magnitudes ~ O(sqrt q)).
"""
import math, cmath
from sympy import isprime

def primitive_root(p):
    # find a generator of F_p^*
    from sympy import factorint
    phi = p - 1
    facs = list(factorint(phi).keys())
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs):
            return g
    raise RuntimeError("no prim root")

def find_prime(n, beta, count=1, start_mult=None):
    """primes p = 1 mod n with p ~ n^beta, return up to `count` of them."""
    target = int(round(n**beta))
    out = []
    # search upward from a multiple of n near target
    k = max(2, target // n)
    while len(out) < count and k < target//n + 200000:
        p = k*n + 1
        if p > 1 and isprime(p):
            out.append(p)
        k += 1
    return out

def subgroup(p, n):
    """the unique order-n multiplicative subgroup mu_n of F_p^*."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # element of order n
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x*h) % p
    assert len(set(S)) == n, "subgroup wrong size"
    return S

def all_periods(p, n, S):
    """eta_b = sum_{y in S} exp(2 pi i b y / p) for b in F_p; return magnitudes."""
    w = 2*math.pi/p
    mags = []
    for b in range(p):
        z = 0j
        bw = (b*w)
        for y in S:
            z += cmath.exp(1j*bw*y)
        mags.append(abs(z))
    return mags

def max_period_b_nonzero(p, n, S):
    """max_{b != 0} ||eta_b||  (b=0 gives eta=n trivially, exclude)."""
    w = 2*math.pi/p
    best = 0.0
    argb = 0
    for b in range(1, p):
        z = 0j
        bw = b*w
        for y in S:
            z += cmath.exp(1j*bw*y)
        m = abs(z)
        if m > best:
            best = m; argb = b
    return best, argb

print("="*108)
print("C063: per-period (3q)^{1/4} sqrt(n) bound vs extreme-value sqrt(n log m), m=(p-1)/n")
print("="*108)
hdr = (f"{'n':>4} {'p':>10} {'beta':>5} {'m':>8} | "
       f"{'Bper=(3q)^.25 sqrtn':>20} {'Btarget=sqrt(2n logm)':>22} | "
       f"{'Btrue':>9} {'Btrue/Btgt':>10} {'Btrue/Bper':>11} {'sig2_eff/n':>11}")
print(hdr)
print("-"*108)

# small n so we can do EXACT max over all b at prize-scale beta.
configs = []
for mu in (3, 4, 5):
    n = 2**mu
    for beta in (4.0, 5.0):
        ps = find_prime(n, beta, count=2)
        for p in ps[:2]:
            configs.append((n, p, beta))

rows = []
for (n, p, beta) in configs:
    if p > 4_000_000:   # keep exact-all-b feasible
        continue
    S = subgroup(p, n)
    m = (p-1)//n
    Btrue, argb = max_period_b_nonzero(p, n, S)
    Bper = (3.0*p)**0.25 * math.sqrt(n)
    logm = math.log(m)
    Btarget = math.sqrt(2.0 * n * logm)
    # effective sigma^2 needed so that sqrt(2 sig2 log m) = Btrue:
    sig2_eff = Btrue**2 / (2.0*logm)
    rows.append((n, p, beta, m, Bper, Btarget, Btrue, Btrue/Btarget,
                 Btrue/Bper, sig2_eff/n))
    print(f"{n:>4} {p:>10} {beta:>5.1f} {m:>8} | "
          f"{Bper:>20.2f} {Btarget:>22.3f} | "
          f"{Btrue:>9.3f} {Btrue/Btarget:>10.3f} {Btrue/Bper:>11.4f} {sig2_eff/n:>11.3f}")

print("-"*108)
print("INTERPRETATION:")
print(" (A) Bper/Btarget = (3q)^{1/4} sqrt(n) / sqrt(2n log m) = (3q)^{1/4}/sqrt(2 log m).")
print("     -> this ratio GROWS like q^{1/4} (the per-period bound's surplus). Check:")
for (n, p, beta, m, Bper, Btarget, Btrue, r1, r2, s2) in rows:
    ratio = Bper/Btarget
    pred = (3.0*p)**0.25 / math.sqrt(2.0*math.log(m))
    print(f"     n={n:>3} p={p:>9}  Bper/Btarget={ratio:8.3f}  (3q)^.25/sqrt(2logm)={pred:8.3f}  q^.25={p**0.25:8.2f}")

print()
print(" (B) Btrue/Btarget should be O(1) BOUNDED (lives at extreme-value scale);")
print("     Btrue/Bper should SHRINK like q^{-1/4} (per-period bound is slack).")
if rows:
    r1s = [r[7] for r in rows]   # Btrue/Btarget
    r2s = [r[8] for r in rows]   # Btrue/Bper
    s2s = [r[9] for r in rows]   # sig2_eff/n
    print(f"     Btrue/Btarget  range [{min(r1s):.3f}, {max(r1s):.3f}]  (bounded O(1) => extreme-value scale)")
    print(f"     Btrue/Bper     range [{min(r2s):.4f}, {max(r2s):.4f}]  (small, shrinks with q => per-period slack)")
    print(f"     sig2_eff/n     range [{min(s2s):.3f}, {max(s2s):.3f}]  (O(1) => sigma^2 = O(n), the prize scale)")
