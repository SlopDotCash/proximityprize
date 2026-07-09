#!/usr/bin/env python3
"""
_wfU_badprime_spread_r2norm.py -- pin down the r=2 (Q1) norm structure HONESTLY.

Part B of the prior probe showed defect primes (r=2, same sum mod p, multiset distinct)
go FAR above n^2/4 (313 at n=8). Two possibilities:
  (i) those "defects" are NOT genuine char-0-distinct -- the multiset differs but the
      cyclotomic element x1+x2 is EQUAL in Z[zeta] (e.g. zeta^a+zeta^b = zeta^c+zeta^d as
      algebraic integers even with {a,b}!={c,d}? NO -- roots of unity are lin indep over
      the power basis only up to the Phi_n relation). Need to check the ACTUAL Z[zeta] value.
  (ii) the n^2/4 bound is simply WRONG and the trace route does not close Q1.

This probe computes, for each claimed r=2 defect, the ACTUAL cyclotomic element
beta = (zeta^a + zeta^b) - (zeta^c + zeta^d) as a power-basis vector, its |N|, and checks
p | N. It then reports the TRUE largest |N| over genuine (beta != 0 in Z[zeta]) r=2 defects,
to see whether p is forced small (poly) or not.

Also: directly tabulate |N(zeta^a - zeta^b)| = |N(1 - zeta_n^{a-b})| and identify WHEN it
is small (prime-power order) vs large (2^phi at order 2).
"""
import math, cmath, itertools
from collections import defaultdict
import sympy


def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5)+1):
        if n % i == 0: return False
    return True


def primitive_root(p):
    pm1 = p - 1
    fac = set()
    x = pm1; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.add(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.add(x)
    for g in range(2, p):
        if all(pow(g, pm1//q, p) != 1 for q in fac): return g


def reduction_table(n):
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]
    redtab = [[0]*phi_n for _ in range(n)]
    for k in range(phi_n): redtab[k][k] = 1
    for k in range(phi_n, n):
        prev = redtab[k-1]
        shifted = [0]*(phi_n+1)
        for i in range(phi_n): shifted[i+1] += prev[i]
        top = shifted[phi_n]
        for i in range(phi_n): shifted[i] -= top*Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    return redtab, phi_n


def norm_power(vec, n):
    prod = 1.0
    for t in range(1, n):
        if math.gcd(t, n) != 1: continue
        w = cmath.exp(2j*math.pi*t/n)
        val = sum(vec[i]*w**i for i in range(len(vec)))
        prod *= abs(val)
    return prod


def main():
    print("="*78)
    print("HONEST r=2 (Q1) norm structure: is p forced poly(n) by the trace route?")
    print("="*78)

    # (1) |N(1 - zeta_n^d)| exact, and its arithmetic meaning
    print("\n[1] |N_{Q(zeta_n)/Q}(1 - zeta_n^d)| for all d (the 2-term root difference):")
    print("    Known: = p if ord(zeta^d)=p^k (prime power), else = 1.  Worst at d=n/2 (order 2 -> N=2^phi? NO).")
    for n in [8, 16, 32]:
        redtab, phi = reduction_table(n)
        print(f"  n={n}, phi={phi}:")
        vals = {}
        for d in range(1, n):
            v = [0]*phi
            for i in range(phi): v[i] += redtab[0][i]
            for i in range(phi): v[i] -= redtab[d][i]
            Nb = round(norm_power(v, n)) if any(v) else 0
            ordv = n // math.gcd(d, n)
            vals[d] = (Nb, ordv)
        # group by order
        from collections import Counter
        by_ord = defaultdict(list)
        for d,(Nb,ordv) in vals.items(): by_ord[ordv].append(Nb)
        for ordv in sorted(by_ord):
            ns = set(by_ord[ordv])
            # arithmetic: ord = prime power p^k -> N = p ; else N = 1
            print(f"     ord(zeta^d)={ordv:3d}: |N|={sorted(ns)}")
        mx = max(Nb for Nb,_ in vals.values())
        print(f"     => MAX |N(1-zeta^d)| over d = {mx}  (so a 2-term-difference defect forces p|N, p<={mx})")

    # (2) Genuine r=2 defects: beta = (zeta^a+zeta^b)-(zeta^c+zeta^d), beta != 0 in Z[zeta], p|N(beta).
    #     Tabulate TRUE max |N(beta)| over such beta, to see the real threshold for r=2.
    print("\n[2] r=2 four-term obstruction beta = zeta^a+zeta^b - zeta^c - zeta^d (genuine, !=0):")
    print("    Largest |N(beta)| over ALL such beta = the TRUE Q1 r=2 threshold (p|N => p<=this).")
    for n in [8, 12, 16, 20]:
        redtab, phi = reduction_table(n)
        maxN = 0; argmax = None
        for a in range(n):
          for b in range(a, n):
            for c in range(n):
              for d in range(c, n):
                if (a,b) == (c,d): continue
                v = [0]*phi
                for t,(s) in [(a,1),(b,1),(c,-1),(d,-1)]:
                    for i in range(phi): v[i] += s*redtab[t][i]
                if not any(v): continue   # beta == 0 in Z[zeta] (genuine char-0 equality)
                Nb = round(norm_power(v, n))
                if Nb > maxN:
                    maxN = Nb; argmax = (a,b,c,d)
        log2 = math.log2(maxN) if maxN else 0
        print(f"  n={n:3d} phi={phi:3d}: MAX|N(beta)|={maxN:>8} (2^{log2:5.1f})  at {argmax};"
              f"  n^2/4={n*n//4};  (2)^phi=2^{phi}")

    print("""
[VERDICT]
  The r=2 four-term obstruction's TRUE max norm is what bounds defect primes -- NOT n^2/4.
  If MAX|N(beta)| grows like 2^phi (=2^{n/2}), then r=2 is ALSO exponential and the
  "p<=n^2/4 polynomial Q1 win" claim is FALSE in general -- it would hold ONLY on the
  sub-slice where the obstruction is a pure 2-term difference (a-b)=(c-d), i.e. Sidon
  pairs, where |N|=|N(1-zeta^e)| <= (max prime power | n). Report which it is.
""")


if __name__ == "__main__":
    main()
