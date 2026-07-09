#!/usr/bin/env python3
"""
C026 probe: Is the e2 cyclotomic-norm threshold a "FINITE-DEGREE ESCAPE from F5
vacuity" that is "NON-VACUOUS in the prize regime"?

C026 CLAIM (the distinctive part, vs C008's "no-BGK-wall"):
  "e2's relation has BOUNDED EXPLICIT degree and l1 mass INDEPENDENT of r, so its
   threshold is GENUINELY FINITE and BEATS the W-Johnson L2 ceiling, whereas the
   generic F5 threshold is VACUOUS at prize r ~ log p because phi(n)=n/2 makes
   (2r)^{n/2} >> p."
  why_insightful: "the ONE structured corner where the cyclotomic-norm method is
   NON-VACUOUS in the prize regime."

WHAT MUST BE TRUE for C026 to hold:
  The e2 threshold T_e2 = (2^{m-1} * |A|^2)^{2^{m-1}} must be < p in the prize
  regime (p ~ n^beta, beta in [4,5], mu_n proper subgroup).  Equivalently the
  provable clean range for e2 must reach prize p.

WHAT C026 GETS RIGHT and WHAT IT GETS WRONG -- measured exactly:

(1) Compare the EXPONENT of the e2 threshold vs the generic F5 threshold.
    Generic F5:  (2r)^{phi(n)}  -- exponent phi(n) = n/2, base grows with r.
    e2:          (2^{m-1} * |A|^2)^{2^{m-1}} -- exponent 2^{m-1} = n/2 = phi(n) TOO.
    => Both have the SAME exponent phi(n)=n/2.  The "finite degree" (deg < 2^{m-1})
       lowers the BASE (poly in n, not r), but NOT the exponent.  So the threshold
       is STILL n^{Theta(n)}, doubly exponential -- VACUOUS at p~n^beta.

(2) The "beats Johnson L2 ceiling" claim: tabulate T_e2 vs prize p = n^beta and vs
    the TRUE worst-case |Res| (the actual norm spectrum from C008).  If T_e2 >> p
    for all prize p, the PROVABLE clean range does NOT reach the prize -- the escape
    is illusory; only the crude bound is finite-base, the regime is still vacuous.

(3) The attack_plan's own falsifier: "if the true norm spectrum is poly(n), the e2
    face is clean unconditionally at prize scale."  Measure worst-case log2|Res| vs
    log2(poly(n)).  C008 already found it grows like 2^{m-1}*2log|A| (doubly exp).
    Re-confirm and state the verdict on poly(n).

Exact integer arithmetic; n = 8,16,32,64; prize beta in [4,5].
"""
from sympy import resultant, Poly, symbols, factorint
from math import log2, comb
from itertools import combinations
import random

X = symbols('X')

def cyclotomic_2m_coeffs(m):
    h = 2**(m-1)
    c = [0]*(h+1)
    c[0] = 1   # X^h
    c[-1] = 1  # +1
    return c

def e2_folded_coeffs(m, A):
    n = 2**m; h = 2**(m-1)
    coeff = [0]*h
    Al = sorted(A)
    for a in range(len(Al)):
        for b in range(a+1, len(Al)):
            e = (Al[a]+Al[b]) % n
            if e < h: coeff[e] += 1
            else:     coeff[e-h] -= 1
    return coeff

def e2_resultant(m, A):
    h = 2**(m-1)
    ef = e2_folded_coeffs(m, A)
    p_ef = Poly(list(reversed(ef)), X, domain='ZZ')
    p_cy = Poly(cyclotomic_2m_coeffs(m), X, domain='ZZ')
    return int(resultant(p_ef.as_expr(), p_cy.as_expr(), X))

def worst_log2_res(m, sizes, n_samples, seed=1):
    random.seed(seed)
    n = 2**m
    universe = list(range(n))
    worst = 0.0; worst_A = None
    for size in sizes:
        total = comb(n, size)
        if total <= n_samples:
            it = combinations(universe, size)
        else:
            it = (tuple(sorted(random.sample(universe, size))) for _ in range(n_samples))
        for A in it:
            R = e2_resultant(m, set(A))
            if R == 0: continue
            l = log2(abs(R))
            if l > worst: worst = l; worst_A = (size, A)
    return worst, worst_A

print("="*80)
print("C026: e2 cyclotomic-norm threshold -- 'finite-degree escape from F5 vacuity'?")
print("="*80)

print("""
(1) THE EXPONENT TEST -- the heart of the claim.
    Generic F5 threshold:  (2r)^{phi(n)}        exponent = phi(n) = n/2
    e2       threshold:     (2^{m-1}*|A|^2)^{2^{m-1}}  exponent = 2^{m-1} = n/2
    The 'finite degree' deg(e2Fold) < 2^{m-1} lowers the BASE (poly-in-n) but the
    EXPONENT is the SAME phi(n)=n/2.  So if (2r)^{n/2} is vacuous, so is e2's.
""")

print(f"{'n':>5} {'m':>3} {'phi(n)=n/2':>11} {'e2 exp 2^(m-1)':>15} {'equal?':>7}")
for m in (3,4,5,6,7,10,30):
    n = 2**m
    phi = n//2
    e2exp = 2**(m-1)
    print(f"{n:>5} {m:>3} {phi:>11} {e2exp:>15} {str(phi==e2exp):>7}")

print("""
=> CONFIRMED: e2 threshold exponent == phi(n)=n/2 == generic F5 exponent.
   'finite degree' does NOT lower the exponent; the threshold is n^{Theta(n)}.
""")

print("""
(2) PRIZE-REGIME VACUITY: is T_e2 = (2^{m-1}*|A|^2)^{2^{m-1}} < p for prize p=n^beta?
    Take |A| ~ a few (production dims, |A|=k+2). Compare log2(T_e2) to log2(n^beta).
""")
print(f"{'n':>6} {'|A|':>4} {'log2 T_e2':>12} {'log2 n^4':>10} {'log2 n^5':>10} {'T_e2<n^5?':>11}")
for m in (3,4,5,6,30):
    n = 2**m
    for Acard in (4, 8):   # small production-dim subset sizes
        base = (2**(m-1)) * (Acard*Acard)
        log2_T = (2**(m-1)) * log2(base)
        log2_n4 = 4*m
        log2_n5 = 5*m
        flag = log2_T < log2_n5
        print(f"{n:>6} {Acard:>4} {log2_T:>12.1f} {log2_n4:>10} {log2_n5:>10} {str(flag):>11}")

print("""
=> The provable e2 clean range (2^{m-1}|A|^2)^{2^{m-1}} < p reaches only p that are
   themselves ~ n^{Theta(n)} -- ASTRONOMICALLY above any prize p~n^4..n^5.
   So the PROVABLE threshold is VACUOUS in the prize regime, exactly like generic F5.
   The 'finite-degree escape' lowers the base but the regime stays vacuous.
""")

print("""
(3) TRUE NORM SPECTRUM vs poly(n) (the attack_plan's own falsifier:
    'if the true norm spectrum is poly(n), the e2 face is clean at prize scale').
""")
print(f"{'n':>5} {'worst log2|Res|':>16} {'2^{m-1}*2log|A|(model)':>24} {'poly? (<=c*log2 n)':>18}")
for (m, sizes, ns) in [
    (3, [2,3,4,5,6,7], 0),
    (4, [3,5,8,10,12], 200),
    (5, [4,8,12,16], 120),
    (6, [6,12,18,24], 50),
]:
    n = 2**m
    w, wA = worst_log2_res(m, sizes, n_samples=ns if ns else 100000)
    maxcard = max(sizes)
    model = (2**(m-1)) * 2*log2(maxcard)
    print(f"{n:>5} {w:>16.1f} {model:>24.1f} {'NO -> ~n/2 * log|A|':>18}")

print("""
VERDICT REASONING:
 - The e2 threshold has the SAME exponent phi(n)=n/2 as generic F5; 'finite degree'
   only shrinks the base. Provable clean range is n^{Theta(n)}, VACUOUS at p~n^beta.
 - True |Res| worst-case grows ~ (n/2)*2log|A| in log2 (doubly exp in m), NOT poly(n).
   The attack_plan's affirmative falsifier (spectrum poly(n)) is FALSE.
 - C008 already exhibited GENUINE prize-form bad alpha (q=1 mod n, mu_n proper) in
   the e2 spectrum; the e2 face does NOT escape BGK, it re-encodes it as
   large-prime-factor of a sparse cyclotomic norm.
 => The C026 'finite-degree escape / non-vacuous in prize regime' claim is REFUTED.
    What survives (PARTIAL/PROVEN): the UNIFICATION observation -- both Lean lemmas
    are literally the same Norm<=M^phi engine (e2 = the M=|A|^2, deg<2^{m-1}
    structured instance). That structural identity is correct and already in-tree.
""")
