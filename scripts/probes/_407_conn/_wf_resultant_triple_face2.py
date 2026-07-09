#!/usr/bin/env python3
"""
C013 probe v2: CONSTRUCT a genuine mod-p anomaly collision at a PRIZE-REGIME
proper-subgroup prime and verify all three Rosetta-stone faces on the SAME integer R.

Construction of a real anomaly: pick a primitive complex n-th root has |g(omega)|<=2r
but g != 0 in char 0; we need g(zeta)==0 mod p for a primitive n-th root zeta of Z/p.
A clean way to GUARANTEE a mod-p collision while staying char-0-nonzero: solve the
linear congruence directly. Take g = X^a + X^b - X^c - X^d (4-term, r=2). Then
   g(zeta) = zeta^a + zeta^b - zeta^c - zeta^d (mod p).
We search exponents a,b,c,d in [0,n) with {a,b} != {c,d} (so char-0 nonzero / R!=0,
the C-Sidon property proven in CyclotomicResultantBound) but the sum == 0 mod p
(a mod-p coincidence = the F12 anomaly, which CANNOT happen in char 0 by Sidon).

For each found anomaly we report the SINGLE integer R and confirm:
  F5/F13 (char-0):  R != 0          (no char-0 collision)
  F12 (char-p):     p | R           (mod-p anomaly collision)
  F11 (ideal-SVP):  |R| = N(alpha), 𝔭 | alpha, |R| <= (2r)^{phi(n)} (box);
                    'short' means the prime sublattice 𝔭 meets the 2r-box.
This demonstrates the Rosetta-stone IDENTITY is REAL: one R, three readings.
"""
import sympy
from sympy import isprime, totient, resultant, Poly, symbols, cyclotomic_poly
import itertools

X = symbols('X')

def prize_primes(n, beta_lo=4.0, beta_hi=5.5, count=2):
    lo, hi = int(n**beta_lo), int(n**beta_hi)
    out = []
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi and len(out) < count:
        if isprime(p) and (p-1) % n == 0 and n*n < p and n < p-1:
            out.append(p)
        p += n
    return out

def primitive_nth_root_modp(p, n):
    g = int(sympy.primitive_root(p))
    return pow(g, (p-1)//n, p)

def Res_Phi_g_int(n, gpoly):
    Phi = cyclotomic_poly(n, X)
    return int(resultant(Phi, gpoly, X))

print("="*78)
print("C013 v2: construct REAL mod-p anomaly; verify one R has all 3 faces")
print("="*78)

any_found = False
for mu in (3,4,5):              # n = 8,16,32
    n = 2**mu
    phin = int(totient(n))
    ps = prize_primes(n)
    for p in ps:
        zeta = primitive_nth_root_modp(p, n)
        # search 4-term anomalies: zeta^a+zeta^b-zeta^c-zeta^d == 0 mod p, {a,b}!={c,d}
        zpow = [pow(zeta, k, p) for k in range(n)]
        found = None
        n_modp_coincidence = 0
        n_char0_collision = 0
        for a,b,c,d in itertools.product(range(n), repeat=4):
            if {a,b} == {c,d}: continue
            if (zpow[a]+zpow[b]-zpow[c]-zpow[d]) % p == 0:
                n_modp_coincidence += 1
                # is it a TRUE char-p anomaly (R!=0) or a char-0 collision (R==0)?
                g = X**a + X**b - X**c - X**d
                R = Res_Phi_g_int(n, g)
                if R == 0:
                    n_char0_collision += 1
                elif found is None:
                    found = (a,b,c,d,R)   # TRUE anomaly: p|R, R!=0
        print(f"\nn={n} p={p} zeta={zeta}: 4-term mod-p coincidences={n_modp_coincidence}, "
              f"of which char-0 collisions (R==0)={n_char0_collision}, "
              f"true char-p anomalies (R!=0)={n_modp_coincidence-n_char0_collision}")
        if found is None:
            print(f"   => NO true r=2 anomaly at prize prime: regime CLEAN at r=2 "
                  f"(every mod-p coincidence is a genuine char-0 collision).")
            continue
        a,b,c,d,R = found
        any_found = True
        ratio = abs(R)/p
        print(f"   TRUE ANOMALY g = X^{a}+X^{b}-X^{c}-X^{d}")
        print(f"   ONE integer R = Res(Phi_n,g) = N(alpha) = {R}")
        print(f"   F5/F13 char-0 collision  (R==0)?           {R==0}  (False = C-Sidon holds)")
        print(f"   F12 char-p anomaly       (p|R and R!=0)?   {R%p==0 and R!=0}")
        print(f"   F11 ideal-SVP: |R|/p = {ratio:.2f}; |R| <= (2r=4)^phi(n)={4**phin}? "
              f"{abs(R)<=4**phin}")

print("\n" + "-"*78)
print(f"any 4-term (r=2) anomaly found at a prize prime? {any_found}")
print("If NONE: the prize regime is CLEAN at r=2 (no char-p anomaly), so the three")
print("faces co-occur only at LARGER r where (2r)^{phi(n)} >= p, i.e. the OPEN wall.")
print("This is exactly the docstring honesty note: threshold VACUOUS for r=O(1).")
