#!/usr/bin/env python3
"""
_wfU_badprime_spread_subfield.py -- the ACTUAL polynomial mechanism: SUBFIELD descent.

The trace identity in the lens is  Tr(beta * conj(beta)) = (n/2)*|B|  -- a DEGREE-2 trace
(beta and its complex conjugate), NOT the full phi-degree norm. This only forces a POLYNOMIAL
prime bound if beta lives in (or its relevant norm descends to) a SMALL-degree subfield, so
that p | N_{L/Q}(beta) with [L:Q] = O(1) instead of [Q(zeta_n):Q] = phi = n/2.

The full-cyclotomic norm N_{Q(zeta_n)/Q} has exponent phi/2 (EXPONENTIAL, confirmed). But the
B-object (the Gauss-period / Paley eigenvalue eta_b) lives in the DECOMPOSITION FIELD -- the
degree-m subfield fixed by the subgroup mu_n, where m=(p-1)/n... NO. Let me get this right:

  eta_b = sum_{y in mu_n} psi(by)  is a GAUSS PERIOD. The n Gauss periods generate the unique
  degree-(p-1)/n ... actually the field of Gauss periods Q(eta) has degree = number of distinct
  periods = the index, and B is an ALGEBRAIC INTEGER of degree dividing that.

The polynomial-threshold question: for WHICH gates is the relevant algebraic integer of
BOUNDED degree (so p | N forces p <= (size)^{O(1)})?  This probe computes the actual DEGREE
of the minimal polynomial of the obstruction beta over Q for each gate, and the norm DOWN TO
that minimal field, to find where the exponent is O(1).

We test: beta_r := a balanced r-sum DIFFERENCE. Its degree over Q = phi(n)/|stab|. The
'r=2 Sidon' object zeta^a - zeta^b = zeta^a(1 - zeta^{b-a}) has the SAME degree as 1-zeta^e
-- still phi(n). So NO subfield collapse there. The genuine degree-2 object is when beta is
fixed by complex conjugation composed with the full Galois group EXCEPT conjugation -- i.e.
beta in the QUADRATIC subfield Q(sqrt(+-n)). That happens for GAUSS SUMS (tau(chi)), not for
generic root-sums. Let's find which gate's beta is genuinely low-degree.
"""
import math, cmath
import sympy
from sympy import minimal_polynomial, sqrt, exp, I, pi, Rational, nsimplify


def degree_of_rootsum(exps, signs, n):
    """Minimal-polynomial degree over Q of beta = sum_i signs[i]*zeta_n^{exps[i]}."""
    zeta = exp(2*I*pi/n)
    beta = sum(s*zeta**e for e, s in zip(exps, signs))
    beta = sympy.expand(beta)
    try:
        mp = minimal_polynomial(beta, sympy.Symbol('x'))
        return sympy.Poly(mp, sympy.Symbol('x')).degree()
    except Exception as ex:
        return -1


def main():
    print("="*78)
    print("SUBFIELD DESCENT: where is the obstruction beta GENUINELY low-degree?")
    print("(only then does p|N(beta) force a POLYNOMIAL p, since exponent = deg/2)")
    print("="*78)

    print("\n[1] Degree over Q of the r-sum obstruction beta (small n, exact via sympy):")
    print("    gate object                              deg(beta)/Q   phi(n)   exponent in p<= |N|^{1}")
    cases = [
        ("r=2 Sidon diff  zeta^0 - zeta^1",      [0,1],     [1,-1],  8),
        ("r=2 4-term      z^0+z^1-z^2-z^3",       [0,1,2,3], [1,1,-1,-1], 8),
        ("r=2 Sidon diff (n=16)",                 [0,1],     [1,-1],  16),
        ("r=3 6-term (n=16)",                     [0,1,2,3,4,5],[1,1,1,-1,-1,-1],16),
        ("Gauss sum tau over mu_2 (=sqrt disc)",  [0,1],     [1,-1],  3),   # 1-omega in Q(sqrt-3): deg 2
    ]
    for name, exps, signs, n in cases:
        d = degree_of_rootsum(exps, signs, n)
        phi = sum(1 for i in range(1,n) if math.gcd(i,n)==1)
        print(f"    {name:42s}  {d:>4}        {phi:>4}     phi-th-power={'POLY' if d<=4 else 'EXP(=deg/2)'}")

    print("""
[2] THE KEY ARITHMETIC FACT (the real reason r=2/d=4 is 'rigorous'):
    The r=2 obstruction beta is a root-of-unity DIFFERENCE (or 4-term sum), of degree phi(n)
    over Q -- it does NOT live in a bounded-degree subfield. So p | N_{Q(zeta_n)/Q}(beta)
    forces only p <= |N| ~ 2^{phi}, EXPONENTIAL, same as every other r.

    The 'Tr(beta conj beta) = (n/2)|B|' identity is the PARSEVAL/trace identity (E1), a SUM
    over conjugates -- it bounds the ARITHMETIC MEAN of |sigma_i(beta)|^2 by a constant (2r).
    But |N|^2 = PRODUCT of |sigma_i|^2 = GEOMETRIC mean ^ phi, and AM>=GM only gives
    |N| <= (AM)^{phi/2}: the phi/2 power is UNAVOIDABLE. There is NO degree-2 norm to exploit
    unless beta is genuinely quadratic (Gauss-sum case), which the root-sum obstruction is not.

[3] CONCLUSION FOR THE LENS:
    The claim 'p <= n^2/4 closes Q1 char-p with a POLYNOMIAL threshold' does NOT hold for the
    full-degree cyclotomic obstruction (numerics: max|N| ~ 2^{phi} for r=2 AND r=3, AM-GM tight).
    It can hold ONLY in one of:
      (a) FIXED small n (then phi=O(1) and any exponent is a constant) -- matches 'd in {4,8}'
          if d=4 means n is held to a small fixed value, NOT the prize n=2^30.
      (b) a genuinely degree-2 object (Gauss sum tau, |tau|^2 = p) -- but that's the SAME wall
          (tau flat, the open core), not a new win.
    => The Q1 polynomial win does NOT replicate on Q2/Q3/Q4/E_r/lacunary at GROWING n. The
    common machinery (norm + trace + AM-GM) shares the phi/2 EXPONENTIAL exponent across ALL
    of them. The only 'polynomial' regime is fixed-tiny-n, where it is polynomial for ALL gates
    equally (no gate is privileged). This is a UNIFICATION (one exponent governs all) but a
    NEGATIVE one: NO second gate inherits a poly threshold the others lack.
""")


if __name__ == "__main__":
    main()
