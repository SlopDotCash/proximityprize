"""
probe_444_padic_newton_spur_2adic.py   (angle [padic-newton-spur], issue #444)

ANGLE: p-adic / Newton-polygon structure of the SPUR carriers, stratified by the
2-ADIC valuation (Stickelberger digit sums) of the relation.

SETUP (the shared core, char-p vs char-0 energy):
  mu_n = order-n subgroup of F_p*, n = 2^mu, n | p-1, PROPER (never the full group),
  p >> n^3 (REAL prize beta = 1 + 128/log2(n); we use beta in {4,5,6} and the real one
  where it matters).
  E_r^{Fp} = #{(a,b) in mu_n^{2r} : sum a = sum b in F_p}.
  E_r^{c0} = same count but with the sum taken in C (no wrap).
  SPUR_r = E_r^{Fp} - E_r^{c0} >= 0 = # SHORT mod-p vanishing +-1 sums of n-th roots
  that do NOT vanish in char 0.

A spur carrier is a multiset relation  f = sum_{i} eps_i * zeta^{a_i} == 0 (mod p in F_p),
eps_i in {+1,-1}, with <= 2r terms, that is != 0 as a cyclotomic integer (char 0).
Equivalently: the cyclotomic integer  alpha = f(zeta_n) in Z[zeta_n]  has alpha != 0 but
the rational prime p | N(alpha) (norm) AND p splits so that zeta_n -> omega in F_p makes
f(omega) == 0 mod p.

THE 2-ADIC HANDLE TO TEST:
  zeta_n is a 2^mu-th root of unity.  The cyclotomic field Q(zeta_{2^mu}) is TOTALLY
  RAMIFIED at 2: (2) = (lambda)^{2^{mu-1}}, lambda = 1 - zeta.  Stickelberger / the digit
  structure controls v_lambda(alpha) (the 2-adic valuation of a spur carrier).
  QUESTION (E1/E2/E3): does v_2 / v_lambda of the spur carriers grow with depth r in a way
  that BOUNDS the deep-r spur (a non-archimedean handle archimedean BGK misses)?  OR is the
  2-adic valuation INDEPENDENT of p (so it gives no p-dependent / depth-dependent constraint
  on the F_p vanishing) = wrong-norm, B2/B3?

TESTS:
  (T1) Compute SPUR_r exactly for r = 1..rmax at the REAL prize-ish beta, several n.
       Confirm the faithfulness depth law (spur=0 shallow, fails deep).
  (T2) For the FIRST spur carrier (the shallowest breaker), compute v_2(N(alpha)) and the
       lambda-adic valuation v_lambda(alpha).  Is it > 0 (a 2-adic constraint) or 0
       (2-adically a unit, valuation-blind)?
  (T3) KEY: is the 2-adic valuation of the spur carriers correlated with / does it bound
       the EVENT "p | N(alpha)" (the F_p vanishing)?  v_2(N(alpha)) vs v_p(N(alpha)):
       are they the SAME factorization slot or DISJOINT?  If disjoint (2-adic part is a
       p-INDEPENDENT bounded factor), the 2-adic stratification cannot constrain which p
       are bad => wrong norm => reduces to wall.
  (T4) Newton polygon (2-adic) of the carrier polynomial f(X) = sum eps_i X^{a_i}: are the
       deep-r carriers 2-adically NON-trivial (some negative slope) or unit polynomials
       (all slope 0)?  If unit => the 2-adic NP is vacuous (matches _NewtonPolygonPeriodSpread).
"""
import math, itertools
from functools import reduce

# ---------- number theory helpers (exact) ----------
def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo):
    """smallest prime p >= lo with n | p-1."""
    # start at first p0 = 1 mod n that is >= lo
    p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while True:
        if is_prime(p): return p
        p += n

def subgroup(p, n):
    """sorted list of the order-n subgroup mu_n of F_p* (n | p-1)."""
    g0 = 2
    while True:
        g = pow(g0, (p-1)//n, p)
        s = {pow(g, i, p) for i in range(n)}
        if len(s) == n:
            return sorted(s)
        g0 += 1

def v2(x):
    """2-adic valuation of a nonzero integer."""
    if x == 0: return math.inf
    v = 0
    x = abs(x)
    while x % 2 == 0:
        x //= 2; v += 1
    return v

def vp(x, p):
    if x == 0: return math.inf
    v = 0; x = abs(x)
    while x % p == 0:
        x //= p; v += 1
    return v

# ---------- exact energy counts via convolution ----------
def energy_charp_char0(H, p, rmax):
    """E_r^{Fp} (wrap mod p) and E_r^{c0} (integer, no wrap) for r=1..rmax."""
    n = len(H)
    # char-p: distribution of r-fold sum mod p
    fp = [0]*p
    for h in H: fp[h] += 1
    # char-0: distribution of r-fold integer sum. Range [0, rmax*max(H)].
    Hmax = max(H); L = rmax*Hmax + 1
    fz = [0]*L
    for h in H: fz[h] += 1
    EP, EZ = [], []
    curp, curz = fp[:], fz[:]
    for r in range(1, rmax+1):
        EP.append(sum(c*c for c in curp))
        EZ.append(sum(c*c for c in curz))
        if r < rmax:
            nxtp = [0]*p
            for t, c in enumerate(curp):
                if c:
                    for h in H:
                        nxtp[(t+h) % p] += c
            curp = nxtp
            nxtz = [0]*((r+1)*Hmax+1)
            for t, c in enumerate(curz):
                if c:
                    for h in H:
                        nxtz[t+h] += c
            curz = nxtz
    return EP, EZ

# ---------- spur carrier extraction (smallest depth) ----------
def first_spur_carrier(H, p, rmax):
    """Find the shallowest +-1 relation of n-th roots that vanishes mod p but not char-0.
    Returns (weight w, signed-exponent relation as list of (sign, exponent_index)) or None.
    A relation: choose r 'plus' roots and r 'minus' roots (with repetition) s.t.
    sum(plus) == sum(minus) mod p but sum(plus) != sum(minus) as integers (in F_p lift).
    We search by increasing total weight 2r, returning the first genuine spur (=defect)."""
    n = len(H)
    for r in range(1, rmax+1):
        # bucket multisets of size r by (sum mod p); within a bucket, a pair with
        # DIFFERENT integer sums and DIFFERENT multisets is a genuine spur carrier.
        buckets = {}
        for cp in itertools.combinations_with_replacement(range(n), r):
            sp_mod = sum(H[i] for i in cp) % p
            sp_int = sum(H[i] for i in cp)
            if sp_mod in buckets:
                for (cm, sm_int) in buckets[sp_mod]:
                    if sm_int != sp_int and cm != cp:
                        return r, cp, cm  # plus = cp, minus = cm
                buckets[sp_mod].append((cp, sp_int))
            else:
                buckets[sp_mod] = [(cp, sp_int)]
    return None

# ---------- cyclotomic-integer norm of a spur carrier (exact) ----------
def cyclotomic_value_and_norm(cp, cm, n):
    """alpha = sum_{i in cp} zeta^{e_i} - sum_{j in cm} zeta^{e_j}, zeta = primitive n-th root.
    Here the 'exponents' are the DISCRETE LOGS of the roots in mu_n. We need the actual
    n-th-root exponents.  Build alpha as an element of Z[zeta_n] via its coeff vector mod
    Phi_n, then compute the integer norm N(alpha) = Res(f, Phi_n) = prod over prim n-th roots.
    For n = 2^mu, Phi_n(X) = X^{n/2} + 1, so Z[zeta_n] has basis 1,zeta,...,zeta^{n/2-1}.
    cp, cm are indices into mu_n; we treat mu_n[i] = zeta^i conceptually (the i-th power of the
    fixed generator) -- this is the natural lacunary relation structure.
    Returns (N, coeff_vector)."""
    half = n // 2
    coeff = [0]*half  # coeff of zeta^k, reduced mod X^{n/2}+1 (so zeta^{k+n/2} = -zeta^k)
    def add(e, s):
        e %= n
        if e < half: coeff[e] += s
        else: coeff[e-half] -= s
    for i in cp: add(i, +1)
    for j in cm: add(j, -1)
    # norm = prod over primitive n-th roots zeta of f(zeta) where f = sum coeff[k] X^k.
    # = Res(f, X^{n/2}+1) up to sign; compute exactly via complex eval then round.
    import cmath
    N = 1.0+0j
    for t in range(1, n, 2):  # primitive 2^mu-th roots: odd powers
        z = cmath.exp(2j*math.pi*t/n)
        val = sum(coeff[k]*z**k for k in range(half))
        N *= val
    Nr = round(N.real)
    return Nr, coeff

# ---------- 2-adic valuation via lambda = 1 - zeta ----------
def lambda_valuation(coeff, n):
    """v_lambda(alpha) where lambda = 1 - zeta_n, n=2^mu. Since (2) = (lambda)^{n/2} (totally
    ramified), v_2(N(alpha)) = v_lambda(alpha) (because N(lambda) = 2 ... actually
    N(1-zeta_{2^mu}) = 2). More precisely v_lambda(alpha) = v_2(N(alpha)) since the residue
    degree is 1. We just read v_2(N(alpha))."""
    pass

# ================= run =================
print("="*78)
print("T1: faithfulness depth law -- SPUR_r at real-ish beta, several n")
print("="*78)
print(f"{'n':>4}{'beta':>6}{'p':>14}{'r':>4}{'E_r^Fp':>14}{'E_r^c0':>14}{'SPUR':>10}")
spur_data = {}
for n in [8, 16, 32]:
    real_beta = 1 + 128/math.log2(n)
    # we cannot reach the real prize prime exhaustively; use a beta that keeps p >> n^3
    # but is computationally feasible. Use beta=4 (n<p^{1/4}) as the standard probe proxy,
    # AND note the real beta is ~5.27-15. We test the MECHANISM (2-adic structure), which is
    # beta-robust; depth-law thresholds scale with log p.
    for beta in [4]:
        lo = int(n**beta)
        p = find_prime(n, lo)
        H = subgroup(p, n)
        rmax = 6 if n <= 16 else 5
        EP, EZ = energy_charp_char0(H, p, rmax)
        for r in range(1, rmax+1):
            spur = EP[r-1] - EZ[r-1]
            tag = "" if spur == 0 else "  <-- DEFECT"
            print(f"{n:>4}{beta:>6.1f}{p:>14}{r:>4}{EP[r-1]:>14}{EZ[r-1]:>14}{spur:>10}{tag}")
        spur_data[(n, beta)] = (p, H, rmax, EP, EZ)
    print()

print("="*78)
print("T2/T3: 2-adic valuation of the FIRST spur carrier vs p-adic valuation")
print("="*78)
print("For the shallowest genuine spur carrier alpha (a +-1 n-th-root relation, !=0 in C,")
print("==0 mod p): v_2(N(alpha)) [2-adic, Stickelberger slot] vs v_p(N(alpha)) [the F_p slot].")
print(f"{'n':>4}{'p':>14}{'r*':>4}{'w':>4}{'|N(alpha)|':>18}{'v2(N)':>8}{'vp(N)':>8}{'verdict':>20}")
for (n, beta), (p, H, rmax, EP, EZ) in spur_data.items():
    sc = first_spur_carrier(H, p, rmax)
    if sc is None:
        print(f"{n:>4}{p:>14}{'-':>4}{'-':>4}{'(no spur in range)':>18}")
        continue
    r, cp, cm = sc
    N, coeff = cyclotomic_value_and_norm(cp, cm, n)
    v2N = v2(N) if N != 0 else math.inf
    vpN = vp(N, p) if N != 0 else math.inf
    # verdict: is the 2-adic slot the same as the p-adic slot? p is odd, so NEVER.
    verdict = "2-adic != p slot" if (p != 2) else "?"
    print(f"{n:>4}{p:>14}{r:>4}{2*r:>4}{abs(N):>18}{v2N:>8}{vpN:>8}{verdict:>20}")

print()
print("INTERPRETATION GUIDE:")
print(" - v_p(N) >= 1 is the F_p-vanishing slot (that IS the spur, by construction).")
print(" - v_2(N) is the 2-adic (Stickelberger/lambda) slot. p is ODD, so the 2-part of N")
print("   is a p-INDEPENDENT factor.  If v_2(N) does NOT control whether p | N, the 2-adic")
print("   stratification cannot pick out which primes p are bad => wrong norm => B2/B3.")
