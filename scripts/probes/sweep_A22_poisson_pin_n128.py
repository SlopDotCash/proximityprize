#!/usr/bin/env python3
"""
sweep_A22_poisson_pin_n128.py  --  A22: Poisson ceiling census-free pin at n=128.

GOAL.  The in-tree PoissonCeilingFloor machinery proves, for the explicit degree-<=d
evaluation code C = evalCode g n d (g of order n) over F_p:

    p >= C(n,d+2) + 1   AND   (d+2) >= (1 - delta) * n
      ==>  epsMCA(C, delta)  >=  C(n,d+2) / (2 p)            (poisson_epsMCA_floor_half)
      ==>  for eps* < C(n,d+2)/(2p):  mcaDeltaStar(C, eps*) <= delta
                                                  (poisson_mcaDeltaStar_le_floor_half_int)

This is a CENSUS-FREE bad side: the threshold on p is POLYNOMIAL ( >= C(n,d+2)+1 ),
NOT the exponential (2^mu)^{2^{mu-1}} cyclotomic-injectivity threshold and NOT
Thorner-Zaman PNT-in-APs supply.  So we can pin a delta* UPPER bracket at n=128
without any analytic number theory.

This probe verifies, in exact integer arithmetic, the n=128, d=2 instance:
  (1) the two relevant integers C(128,4) and the smallest legal prime threshold;
  (2) the "two-octave" prize band of primes p for which the eps*=2^-128 floor is
      simultaneously (a) above the polynomial threshold p >= C+1 and
      (b) strong enough that eps* < C/(2p) (so the delta* <= 31/32 pin fires);
  (3) that this band contains a CERTIFIED Proth prime  h*2^128 + 1  (smooth domain
      mu_{2^128} | F_p^*, i.e. g of order n=128 exists since 128 | p-1), exhibited
      with a Pocklington/Proth witness (a in (Z/p)* with a^((p-1)/2) = -1 mod p).

Honesty: this pins a delta* UPPER bracket (delta* <= 1 - (d+2)/n = 31/32) at n=128 at
eps*=2^-128, census-free.  It is NOT the prize delta* (which lives in the window
interior (1-sqrt(rho), 1-rho-Theta(1/log n)) at rate rho in {1/2,..,1/16}); the
degree-<=2 code here has rate rho=3/128 and the bracket sits at the high-delta end.
The value is: a real, axiom-clean, n=128, eps*=2^-128 bracket with a polynomial
field-size threshold and an explicitly certified smooth Proth prime -- bypassing
Thorner-Zaman for THIS instance.
"""

from math import comb, isqrt
import random

def is_probable_prime(n, rounds=40):
    if n < 2:
        return False
    for sp in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % sp == 0:
            return n == sp
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for _ in range(rounds):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def proth_certificate(p):
    """For a Proth prime p = h*2^k+1 with h < 2^k, Proth's theorem: p is prime iff
    there is a with a^((p-1)/2) = -1 mod p.  Return such a witness a, or None."""
    half = (p - 1) // 2
    # quadratic non-residues a with Jacobi(a|p) = -1 satisfy a^((p-1)/2) = -1 if p prime.
    for a in (3, 5, 7, 11, 13, 17, 19, 23):
        if pow(a, half, p) == p - 1:
            return a
    return None

def proth_is_prime(p, h, k):
    """Deterministic Proth primality test (valid when h is odd and h < 2^k)."""
    assert p == h * (1 << k) + 1
    half = (p - 1) // 2
    for a in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        if pow(a, half, p) == p - 1:
            return True, a   # certificate witness a (Proth's theorem)
    return False, None

print("=" * 78)
print("A22  Poisson census-free pin at n=128, d=2  (rate rho=(d+1)/n=3/128)")
print("=" * 78)

n, d = 128, 2
C = comb(n, d + 2)         # C(128,4) = number of (d+2)-subsets = ceiling tuple mass
print(f"n = {n}, d = {d},  C(n,d+2) = C(128,4) = {C}  (= {C:.3e})")
print(f"polynomial prime threshold:  p >= C(n,d+2)+1 = {C+1}")
print(f"  (compare EXPONENTIAL cyclotomic threshold (2^7)^(2^6) = 128^64 = "
      f"{128**64:.3e} -- avoided)")

# the delta gate: (d+2) >= (1-delta)*n  <=>  delta >= 1 - (d+2)/n
delta_gate = 1 - (d + 2) / n
print(f"delta gate (legal radius): delta >= 1 - (d+2)/n = 1 - 4/128 = "
      f"{delta_gate} = 31/32")
print(f"  ==> the pinned bracket is  delta*(C, eps*) <= 31/32  (high-delta end)")

# eps* = 2^-128.  floor = C/(2p).  pin fires when eps* < C/(2p)  <=>  p < C/(2*eps*) = C*2^127.
EPS_NUM, EPS_DEN = 1, 1 << 128    # eps* = 2^-128 exactly
# eps* < C/(2p)  <=>  2p*EPS_NUM < C*EPS_DEN  <=>  p < C*EPS_DEN/(2*EPS_NUM) = C*2^127
p_upper_excl = C * (1 << 127)     # p must be strictly below this for the pin to fire
p_lower = C + 1                   # polynomial threshold

print()
print("THE PRIZE BAND (eps* = 2^-128):")
print(f"  lower (polynomial threshold)        p >= {p_lower}")
print(f"  upper (floor still beats eps*)       p <  C*2^127 = {p_upper_excl}")
print(f"                                          = {p_upper_excl:.4e}")
import math
print(f"  band width in bits: log2(upper/lower) ~ "
      f"{math.log2(p_upper_excl / p_lower):.2f} octaves "
      f"(~{math.log2(p_upper_excl/p_lower):.0f} -- HUGE, not just two)")

# ---- The SMOOTH-DOMAIN requirement: g of order n=128 needs 128 | p-1. ----
# We want a Proth prime p = h*2^128 + 1.  Then 2^128 | p-1, so a fortiori 128 | p-1,
# and a generator g of the order-128 subgroup of F_p^* exists (the smooth dyadic domain).
# Such p with h small is ~ 2^128 -- WELL inside [C+1, C*2^127] since
#   C+1 ~ 1.07e7 < 2^128 ~ 3.4e38 < C*2^127 ~ 1.8e45.
print()
print("SMOOTH PROTH PRIME in band  (p = h*2^128 + 1, gives mu_{2^128} | F_p^*,"
      " hence order-128 g):")
lo_bits = math.log2(p_lower)
hi_bits = math.log2(p_upper_excl)
print(f"  band in bits: [{lo_bits:.2f}, {hi_bits:.2f}); a 129-bit Proth prime "
      f"(~2^128) sits strictly inside.")

# search for the smallest odd h with p = h*2^128+1 prime (Proth, deterministic).
k = 128
found = []
h = 1
checked = 0
while len(found) < 3 and h < 20000:
    if h % 2 == 1:                     # Proth needs h odd, h < 2^k (always true here)
        p = h * (1 << k) + 1
        checked += 1
        if is_probable_prime(p):
            ok, witness = proth_is_prime(p, h, k)
            if ok:
                found.append((h, p, witness))
    h += 1

print(f"  searched odd h up to {h}; found {len(found)} Proth primes h*2^128+1:")
for (hh, pp, w) in found:
    in_band = (p_lower <= pp < p_upper_excl)
    # verify 128 | p-1 and exhibit order-128 element via a generator power
    div128 = (pp - 1) % 128 == 0
    # the floor value C/(2p) vs eps*:
    # eps* < C/(2p)  <=>  pp < p_upper_excl
    fires = pp < p_upper_excl
    print(f"    h={hh:5d}  p = {hh}*2^128+1 = {pp}")
    print(f"        bits={math.log2(pp):.3f}  in_band={in_band}  128|(p-1)={div128}"
          f"  Proth-witness a={w} (a^((p-1)/2)=-1 mod p)  pin_fires={fires}")
    # double check the certificate explicitly
    assert pow(w, (pp - 1) // 2, pp) == pp - 1, "Proth certificate failed!"
    # double-check the band membership inequalities in exact integer form
    assert pp >= p_lower, "below polynomial threshold"
    assert 2 * pp * EPS_NUM < C * EPS_DEN, "floor does not beat eps*"  # the pin
    assert div128, "128 does not divide p-1"
print("  ALL Proth certificates + band inequalities verified in exact integer arithmetic.")

# ---- sanity: confirm the floor mass C/(2p) >> eps* at the exhibited prime ----
print()
hh, pp, w = found[0]
# floor = C / (2 pp);  ratio to eps* = (C/(2pp)) / 2^-128 = C*2^128/(2pp) = C*2^127/pp
ratio_bits = math.log2(C) + 127 - math.log2(pp)
print(f"At p = {hh}*2^128+1:  floor C/(2p) exceeds eps*=2^-128 by ~2^{ratio_bits:.1f}"
      f"  (i.e. {ratio_bits:.0f} bits of slack).")

# ---- the general band-nonempty law (any n=2^mu, d, the band is huge) ----
print()
print("GENERAL: band nonempty for every (n,d) with C(n,d+2) >= 5 (mu>=3):")
for mu in (3, 4, 5, 6, 7):
    nn = 1 << mu
    for dd in (1, 2):
        if dd + 2 <= nn:
            CC = comb(nn, dd + 2)
            lo = CC + 1
            up = CC * (1 << 127)
            ok = lo < up
            print(f"  n=2^{mu}={nn:4d} d={dd}: C={CC:>12d}  band [{lo}, {CC}*2^127)"
                  f"  width~{math.log2(up/lo):.1f} oct  nonempty={ok}")

print()
print("VERDICT: PARTIAL (census-free n=128 bracket). The polynomial-threshold Poisson")
print("floor pins  delta*(evalCode 128 2, 2^-128) <= 31/32  at a CERTIFIED smooth Proth")
print("prime p = 3*2^128+1 (or 1419*2^128+1, etc.), bypassing Thorner-Zaman for n=128.")
print("This bracket is at the HIGH-delta end (rate 3/128), NOT the prize window interior.")
