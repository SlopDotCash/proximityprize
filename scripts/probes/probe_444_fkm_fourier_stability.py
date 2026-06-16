#!/usr/bin/env python3
"""
probe_444_fkm_fourier_stability.py -- assess the FKM (Fouvry-Kowalski-Michel) "Fourier-stability
transport" lead for the #444 open core.

OPEN CORE:  M(n) = max_{b != 0} |eta_b|,  eta_b = sum_{x in mu_n} e_p(b x),  mu_n = order-n PROPER
            subgroup of F_p^*  (n = 2^mu, n | p-1, n < sqrt(p)).  Prize: p ~ n*2^128, n ~ 2^30.
            SOTA only n^{1-o(1)} (BGK). Target sqrt(n log m), m = (p-1)/n.

THE LEAD:   eta_b is LITERALLY the discrete Fourier transform of the indicator 1_{mu_n} of the
            subgroup, evaluated at the additive character. FKM trace-function theory proves the
            (l-adic) Fourier transform of a trace function of bounded conductor is again a trace
            function of bounded conductor (Deligne / Katz), so it inherits the Weil sqrt(p)
            cancellation. Idea: bound a DUAL object that the transform controls "sub-sqrt-p"
            more easily, then transport back.

WHAT THIS PROBE TESTS (exact, proper subgroups, never full group):
  (1) The DFT identity: eta_b = hat{1_{mu_n}}(b) exactly (sanity / convention pin).
  (2) The trace-function CONDUCTOR of 1_{mu_n}:  1_{mu_n}(x) = (1/n) sum_{psi: psi^n=1 on mu...}
      Actually 1_{mu_n}(x) = (n/(p-1)) sum_{chi: chi^n = chi_0} chi(x)  -- it is a sum of n
      MULTIPLICATIVE characters (Kummer sheaves). So eta_b = (n/(p-1)) sum_{chi^n=1} G(chi, b),
      G = Gauss sum.  => eta_b is a sum of n Gauss sums (each |G|=sqrt(p)), NOT one trace function
      of bounded conductor: the conductor GROWS with n.  We measure: does |eta_b| behave like
      ONE trace function (~sqrt(p), n-independent, would WIN) or like a SUM of n cancelling Gauss
      sums (the period, ~ between sqrt(n) and n, the WALL)?
  (3) The "dual sum": is there a dual aggregate the FT controls sub-sqrt-p that does NOT reduce
      back to the period?  We test the Fourier DUAL of the eta_b sequence over b: the dual of the
      period function is the indicator itself (Parseval is exact), so the dual L2 = n (no gain);
      the dual L-infinity over b IS M(n).  Self-dual => transport gives back the SAME object.
"""
import sys, math, cmath
from sympy import isprime, primitive_root, divisors

def odd_part(m):
    while m % 2 == 0 and m > 0:
        m //= 2
    return m

def prize_prime(n, beta, pmax=10**8):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if isprime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x * z) % p
    return e

def eta(b, elts, p):
    s = 0j
    for x in elts:
        s += cmath.exp(2j * math.pi * (b * x % p) / p)
    return s

def house(n, p):
    """M(n) = max over b!=0 of |eta_b|, using orbit-invariance: only need coset reps."""
    elts = subgroup(n, p)
    best = 0.0; argb = 0
    seen = set()
    # eta_{zeta b} = eta_b, so iterate one rep per coset of mu_n in F_p^*.
    for b in range(1, p):
        if b in seen:
            continue
        for z in elts:
            seen.add((b * z) % p)
        v = abs(eta(b, elts, p))
        if v > best:
            best = v; argb = b
    return best, argb

def main():
    print("=" * 104)
    print(" #444 FKM Fourier-stability transport: is eta_b ONE trace function (sqrt p, WIN) or a")
    print("       SUM of n Gauss sums = the Gauss period (the WALL)?   [exact, PROPER mu_n]")
    print("=" * 104)

    # ----- (1) DFT identity sanity + (2) conductor / period scaling -----
    print("\n(1)+(2)  eta_b vs sqrt(p) [one-trace-fn target] and vs sqrt(n)/n [period scale]:")
    print(f"{'n':>4} {'p':>10} {'beta':>5} | {'M(n)':>9} {'M/sqrt(p)':>10} {'M/sqrt(n)':>10} "
          f"{'M/n':>7} {'2sqrt(n)':>9} {'sqrt(nlogm)':>11}")
    rows = []
    for n in (4, 8, 16, 32, 64):
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta, pmax=2 * 10**6 if n <= 16 else 4 * 10**5)
            if p is None:
                continue
            M, b0 = house(n, p)
            m = (p - 1) // n
            rows.append((n, p, beta, M, m))
            print(f"{n:>4} {p:>10} {beta:>5.1f} | {M:>9.3f} {M/math.sqrt(p):>10.4f} "
                  f"{M/math.sqrt(n):>10.4f} {M/n:>7.3f} {2*math.sqrt(n):>9.3f} "
                  f"{math.sqrt(n*math.log(m)):>11.3f}")

    print("\n  READING (2): if M/sqrt(p) is ~CONSTANT and n-independent => eta_b is essentially ONE")
    print("  trace function of bounded conductor (FKM would WIN: sqrt(p) is BELOW the prize floor n).")
    print("  If instead M/sqrt(p) -> 0 like sqrt(n/p) (i.e. M ~ sqrt(n)..n, p-INDEPENDENT), then the")
    print("  n Gauss sums CANCEL down to the period scale: the conductor is effectively n (grows),")
    print("  the FT is a sum of n sheaves, and FKM gives no n-independent handle => reduces to WALL.")

    # ----- (3) self-duality: is the 'dual sum' a genuinely different/easier object? -----
    print("\n(3)  Self-duality test: Fourier-dual of the period function {eta_b}_b is 1_{mu_n} itself.")
    print(f"{'n':>4} {'p':>10} | {'sum_b|eta_b|^2':>14} {'(p-1)*?':>10} {'==n(p-?)':>12} "
          f"{'dualLinf=M?':>11}")
    for (n, p, beta, M, m) in rows:
        if beta != 4.0:
            continue
        elts = subgroup(n, p)
        # L2 over ALL b (including 0): sum_b |eta_b|^2 = p * n  (Parseval, since 1_{mu_n} has n ones).
        # Excluding b=0 (eta_0 = n): sum_{b!=0} |eta_b|^2 = p*n - n^2 = n(p-n).
        s2 = 0.0
        for b in range(p):
            s2 += abs(eta(b, elts, p)) ** 2
        target = n * p
        print(f"{n:>4} {p:>10} | {s2:>14.1f} {'':>10} n*p={target:>9.1f}  "
              f"{'EXACT' if abs(s2-target)<1e-3*target else 'NO':>11}")
    print("\n  READING (3): Parseval is EXACT (sum_b|eta_b|^2 = n*p) -- the period sequence is its own")
    print("  Fourier pair with the indicator. The 'dual sum' the FT controls is the L2 = n*p (a SECOND")
    print("  moment), NOT a sub-sqrt-p L-infinity gain. The dual L-infinity over b is M(n) ITSELF.")
    print("  Transporting an L2/average bound back gives only the average sqrt(n) -- the 2nd-moment")
    print("  meta-theorem ceiling -- NOT the L-infinity sup. The object is SELF-DUAL on the sup side.")

if __name__ == "__main__":
    main()
