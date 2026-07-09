#!/usr/bin/env python3
"""
_wfU_badprime_spread_primitive.py -- the DECISIVE test: restrict to PRIMITIVE +-1 relations.

Prior probe found the worst r=2 norm at (0,0,n/2,n/2) = 2(1-zeta^{n/2}), |N| ~ 2^{2phi}.
But that relation has a COEFFICIENT OF MAGNITUDE 2 (it's 2*zeta^0 - 2*zeta^{n/2}); it is the
square of a 1-term object, NOT a genuine 4-distinct-element deep-energy obstruction.

The HONEST Q1/deep-energy obstruction (and the trace-route object beta) is a SIGNED SUM of
2r roots with all coefficients in {-1,0,+1} after collecting -- a *multiplicity-free* signed
relation:  the r=2 case is  zeta^a + zeta^b - zeta^c - zeta^d  with {a,b} disjoint from {c,d}
as multisets (a primitive vanishing relation, the actual additive-energy collision shape).

This probe re-runs Part [2] but ONLY over coefficient vectors c on mu_n with ||c||_inf <= 1
(genuine signed relations), tracking MAX|N(beta)| -- the TRUE Q1 threshold. Then it asks the
same for r=3,4 to see if the polynomial reach is r=2-only or extends.
Also tests: does the trace identity Sum|sigma_i|^2 = (phi)*(something) give |N| <= small via
AM-GM for the multiplicity-free case (where ||c||_2^2 = #terms = 2r is constant)?
"""
import math, cmath, itertools
import sympy
from collections import defaultdict


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


def group_to_power(coeffs_mu, redtab, phi):
    v = [0]*phi
    for t, ct in enumerate(coeffs_mu):
        if ct == 0: continue
        for i in range(phi): v[i] += ct*redtab[t][i]
    return v


def signed_relations(n, r):
    """yield all primitive multiplicity-free signed relations: choose r '+' positions and r '-'
       positions, all distinct (a Sidon-type collision x_+ = x_-). Coeffs in {-1,0,1}."""
    pos_all = range(n)
    for plus in itertools.combinations(pos_all, r):
        rest = [x for x in pos_all if x not in plus]
        for minus in itertools.combinations(rest, r):
            c = [0]*n
            for a in plus: c[a] = 1
            for b in minus: c[b] = -1
            yield c


def main():
    print("="*78)
    print("DECISIVE: PRIMITIVE (multiplicity-free, +-1) signed relations -- TRUE Q1 norm")
    print("="*78)

    print("\n[A] r=2 multiplicity-free obstruction: MAX|N(beta)| over genuine 4-distinct relations")
    for n in [8, 12, 16, 20, 24]:
        redtab, phi = reduction_table(n)
        maxN = 0; argmax = None; cnt_nonzero = 0
        for c in signed_relations(n, 2):
            v = group_to_power(c, redtab, phi)
            if not any(v): continue
            cnt_nonzero += 1
            Nb = round(norm_power(v, n))
            if Nb > maxN: maxN = Nb; argmax = c
        log2 = math.log2(maxN) if maxN else 0
        print(f"  n={n:3d} phi={phi:3d}: MAX|N|={maxN:>8} (2^{log2:5.2f})  n^2={n*n}  n^2/4={n*n//4}  2^phi=2^{phi}")

    print("\n[B] r=3 multiplicity-free obstruction (6 distinct): MAX|N(beta)|")
    for n in [12, 16, 18, 20]:
        redtab, phi = reduction_table(n)
        maxN = 0
        cnt = 0
        for c in signed_relations(n, 3):
            cnt += 1
            if cnt > 200000: break
            v = group_to_power(c, redtab, phi)
            if not any(v): continue
            Nb = round(norm_power(v, n))
            if Nb > maxN: maxN = Nb
        log2 = math.log2(maxN) if maxN else 0
        print(f"  n={n:3d} phi={phi:3d}: MAX|N|={maxN:>10} (2^{log2:5.2f})  n^3={n**3}  2^phi=2^{phi}  [{cnt} rels scanned]")

    print("\n[C] The AM-GM/trace bound for multiplicity-free: ||c||_2^2 = 2r is CONSTANT.")
    print("    AM-GM: |N| <= ((1/phi) Sum|sigma_i|^2)^{phi/2}. For mult-free, Sum|sigma_i|^2 over")
    print("    primitive n-th roots <= phi * (2r) (each |sigma_i(beta)| <= sqrt of... ) -- check the")
    print("    actual MAX of Sum|sigma_i|^2 / phi  (the arithmetic mean of squared conjugate norms):")
    for n in [8, 16, 24]:
        redtab, phi = reduction_table(n)
        worst_am = 0; worst_maxsig = 0
        for c in signed_relations(n, 2):
            v = group_to_power(c, redtab, phi)
            if not any(v): continue
            units = [i for i in range(1,n) if math.gcd(i,n)==1]
            sigs = []
            for i in units:
                w = cmath.exp(2j*math.pi*i/n)
                sigs.append(abs(sum(v[k]*w**k for k in range(phi)))**2)
            am = sum(sigs)/len(sigs)
            worst_am = max(worst_am, am)
            worst_maxsig = max(worst_maxsig, max(sigs))
        print(f"  n={n:3d} phi={phi:3d}: worst arith-mean |sigma|^2={worst_am:6.2f} (2r=4); "
              f"worst single |sigma|^2={worst_maxsig:6.2f}; AM-GM |N|<= {worst_am**(phi/2):.3g} = 2^{(phi/2)*math.log2(max(worst_am,1)):.1f}")

    print("""
[VERDICT] If [A] MAX|N| for multiplicity-free r=2 grows like 2^phi -> exponential, the
  'polynomial p<=n^2/4' is NOT a generic Q1 closure; it is a special sub-case.
  If it stays = O(poly(n)) -> the polynomial win is real for genuine mult-free r=2.
  Compare [A] vs [B]: if r=2 is poly but r=3 explodes, the reach is exactly r=2 (d=4).
""")


if __name__ == "__main__":
    main()
