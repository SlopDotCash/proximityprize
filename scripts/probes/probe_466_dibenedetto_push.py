#!/usr/bin/env python3
"""probe_466_dibenedetto_push.py -- LANE P6 / dossier v3 sec 6 Tier-1 item 5 ("attack #5",
announced 2026-06-27, never run): can the di Benedetto et al. (arXiv 2003.06165)
Bourgain-Garaev chain be pushed to an EFFECTIVE 1/2 exponent at beta = 4 with
structure-aware (mu_n-exact) energy inputs?

METHOD: exact-rational exponent calculus over the FULL parameterized proof shape of
2003.06165 Theorem 3.1 (extracted from the paper in docs/references/
proximity-gap-paley-spectrum/subgroup-expsum-2003.06165.pdf):

  Round i (arity s_i, energy T_{s_i}(H) <= H^{t_i + o(1)}): dyadic pigeonhole +
  Cauchy-Schwarz vs T_{s_i} produce a set with
     |X_i| >~ H^{2 s_i - t_i} * Delta_{i-1}^{2 s_i} / Delta_i^2 ,
     Delta_i in [Delta_{i-1}^{s_i}, 1]   (log-exponents d_i in [s_i d_{i-1}, 0], d_0 = d).
  Final multilinear estimate on the last sets, compared against the amplified lower bound,
  gives ONE linear inequality kappa*beta >= sum_i coeff_i * x_i + d_k with
     trilinear (Macourt / Petridis-Shparlinski, Lemma 4.1): kappa = 1/4,
        coeffs = (1-3/4, 1-3/4, 1-7/8) = (1/4, 1/4, 1/8)   [k = 3 sets]
     bilinear (classical complete-sum Cauchy-Schwarz): kappa = 1/2, coeffs = (1/2, 1/2).
  Elimination of the unknown dyadic levels d_i is the paper's positive-coefficient
  chaining: with x_i = (2 s_i - t_i) + 2 s_i d_{i-1} - 2 d_i, the assembled coefficient
  of d_i is c_i = -2 coeff_i + 2 s_{i+1} coeff_{i+1} (+1 at i = k); where c_i >= 0
  substitute the chained lower bound d_i >= (prod_{j<=i} s_j) d, where c_i < 0 substitute
  d_i <= 0.  Result: kappa*beta >= E + C d with
     E = sum_i coeff_i (2 s_i - t_i),   C = 2 s_1 coeff_1 + sum_i max(c_i, 0) prod_{j<=i} s_j,
  hence Delta <= H^{(kappa*beta - E)/C} and theta(beta) = 1 + (kappa*beta - E)/C.
  (This is EXACTLY the paper's (5.14)->end computation, generalized; all arithmetic in
  fractions.Fraction, no float in the verdict path.)

SELF-TEST: paper parameters (t2 = 49/20 [MRSS Thm 3], t3 = 4 [MRSS Cor 7], Macourt
trilinear, arities (3,3,2)) must give theta(beta) = 1 + (beta - 191/40)/72, i.e.
theta(4) = 1 - 31/2880 and triviality exactly at beta = 191/40 = 4.775.

SWEEPS (at beta = 4; also beta in {3, 4.5, 191/40, 5}):
  (A) PROVEN inputs: t2 = 49/20, t3 = 4, higher t_m by fiber interpolation
      min(2(m-2)+t2, 2(m-3)+t3, 2m-1); all arities (s1,s2,s3) in {2..6}^3 + bilinear
      (s1,s2) in {2..6}^2.  -> best PROVEN exponent of the proof shape.
  (B) STRUCTURE-AWARE "perfect" inputs: char-0-perfect energies t_m = m for ALL m
      (zero wraparound at every depth: T2 = 3n^2-3n, T3 = 15n^3-45n^2+40n leading orders
      extended to all m -- STRICTLY stronger than anything provable off-BGK, since even
      the char-0 ladder has t_m = m only up to constants and char-p adds wraparound).
      -> the STRUCTURAL PLATEAU: what NO energy improvement can beat in this shape.
  (C) INVERSE: with perfect energies + best shape, what multilinear strength (kappa at
      Macourt's coeffs; coeffs at kappa = 1/4) would be NEEDED for theta = 1/2?
      -> quantifies the circularity (a p-power-free multilinear bound IS the open
      sqrt-cancellation).

VERDICT RULE: attack #5 is REFUTED if sweep (B) plateaus at theta >> 1/2; LIVE only if
some shape at proven or char-0-perfect inputs approaches 1/2.  Standing a-priori kill
(in-tree `deltaStar_determination_all_or_nothing`): NO fixed power saving theta > 1/2
moves delta* off Johnson -- this probe quantifies how far the BG shape is from even
that (irrelevant) bar.

Validity gates at beta = 4: MRSS T2/T3 need H < sqrt(p) (true, n = p^{1/4}); Macourt
trilinear unconditional; paper's standing assumption H > p^{1/4} holds at the boundary.
"""

from fractions import Fraction as Fr
from itertools import product

def t_proven(m):
    """Best PROVEN t_m for subgroups H < sqrt(p) (MRSS Thm 3 / Cor 7, logs in o(1));
    m >= 4 by fixing variable pairs: T_m <= H^{2(m-2)} T_2, T_m <= H^{2(m-3)} T_3;
    trivial fiber T_m <= H^{2m-1}."""
    if m == 2:
        return Fr(49, 20)
    if m == 3:
        return Fr(4)
    return min(Fr(2 * (m - 2)) + Fr(49, 20), Fr(2 * (m - 3)) + 4, Fr(2 * m - 1))

def t_perfect(m):
    """Char-0-perfect (zero-wraparound) energies t_m = m: unattainably optimistic."""
    return Fr(m)

def solve_chain(beta, arities, t_of, template):
    """Closed-form exponent of the generalized chain; returns theta or None if >= 1
    (no saving) or the calculus degenerates (C <= 0)."""
    k = len(arities)
    if template == 'trilinear':
        if k != 3:
            return None
        kappa, coeffs = Fr(1, 4), [Fr(1, 4), Fr(1, 4), Fr(1, 8)]
    elif template == 'bilinear':
        if k != 2:
            return None
        kappa, coeffs = Fr(1, 2), [Fr(1, 2), Fr(1, 2)]
    else:
        kappa, coeffs = template  # custom (kappa, [coeff_1..coeff_k])
        if len(coeffs) != k:
            return None
    ts = [t_of(s) for s in arities]
    E = sum(coeffs[i] * (2 * arities[i] - ts[i]) for i in range(k))
    C = 2 * arities[0] * coeffs[0]
    prod_s = Fr(1)
    for j in range(1, k + 1):
        prod_s *= arities[j - 1]
        cj = -2 * coeffs[j - 1]
        if j < k:
            cj += 2 * arities[j] * coeffs[j]
        if j == k:
            cj += 1
        if cj > 0:
            C += cj * prod_s
    if C <= 0:
        return None
    d = (kappa * beta - E) / C
    if d >= 0:
        return None  # no saving proved
    return 1 + d

def theta_biH(beta, s, t):
    """One amplification round (arity s, consuming T_s) + classical bilinear-with-
    coefficients against H itself: H|X|Delta_1 <= (p |X| H)^{1/2}.  Exponent inequality:
    (2s-t)/2 + 1/2 + s*d <= beta/2.  With PERFECT t = s this is EXACTLY
    momentExponent(s, beta) = (beta+s-1)/(2s): the BG chain degenerates to the pure
    moment ladder -- see the DICTIONARY section below."""
    E = (Fr(2 * s) - t) / 2 + Fr(1, 2)
    d = (Fr(beta, 2) - E) / s
    return 1 + d if d < 0 else None

def sweep(beta, t_of, label):
    print(f"\n--- SWEEP [{label}] beta = {beta} ({float(beta):.3f}) ---")
    results = []
    # SOUND shapes only: the LAST round must be the modulus-eliminating pair step
    # (Cauchy-Schwarz on the inner variable, arity 2, consuming T_2); higher/odd last
    # arities change the Hoelder bookkeeping and are NOT modeled.  Middle arities free.
    for s1, s2 in product(range(2, 9), repeat=2):
        th = solve_chain(beta, (s1, s2, 2), t_of, 'trilinear')
        if th is not None:
            results.append((th, (s1, s2, 2), 'tri'))
    for s1 in range(2, 9):
        th = solve_chain(beta, (s1, 2), t_of, 'bilinear')
        if th is not None:
            results.append((th, (s1, 2), 'bi2'))
    for s1 in range(2, 13):
        th = theta_biH(beta, s1, t_of(s1))
        if th is not None:
            results.append((th, (s1,), 'biH'))
    if not results:
        print("  NO chain in the family proves any saving at this beta.")
        return None
    results.sort()
    for th, sh, kind in results[:5]:
        print(f"  theta = {float(th):.6f} = {th}   arities={sh} [{kind}]")
    best = results[0]
    print(f"  BEST: theta = {float(best[0]):.6f} ({best[0]}) at arities {best[1]} [{best[2]}]"
          f"   saving = {float(1-best[0]):.6f}")
    return best

print("=" * 78)
print("SELF-TEST: paper parameters (arities (3,3,2); PROVEN t2=49/20, t3=4; Macourt)")
ok = True
for beta, name in ((Fr(4), "beta=4"), (Fr(191, 40), "beta=191/40 (triviality)"),
                   (Fr(3), "beta=3")):
    th = solve_chain(beta, (3, 3, 2), t_proven, 'trilinear')
    formula = 1 + (beta - Fr(191, 40)) / 72
    match = (th == formula) if th is not None else (formula >= 1)
    ok &= match
    print(f"  {name}: got {th}, paper formula {formula}  {'OK' if match else 'MISMATCH'}")
print(f"  SELF-TEST {'PASS' if ok else 'FAIL'}")
assert ok

for beta in (Fr(3), Fr(4), Fr(9, 2), Fr(5)):
    sweep(beta, t_proven, "A: PROVEN energies (MRSS)")
    sweep(beta, t_perfect, "B: char-0-PERFECT energies t_m = m (unattainable)")

print("\n" + "=" * 78)
print("(C) INVERSE: multilinear strength NEEDED for theta = 1/2 at beta = 4, perfect energies")
best_shape, best_theta = None, None
for s1, s2 in product(range(2, 9), repeat=2):
    s = (s1, s2, 2)
    th = solve_chain(Fr(4), s, t_perfect, 'trilinear')
    if th is not None and (best_theta is None or th < best_theta):
        best_theta, best_shape = th, s
print(f"  best perfect-energy trilinear shape at beta=4: {best_shape}, "
      f"theta = {best_theta} ({float(best_theta):.5f})")

def theta_at(kappa, coeffs):
    th = solve_chain(Fr(4), best_shape, t_perfect, (kappa, coeffs))
    return th

# needed kappa at Macourt coeffs (1/4,1/4,1/8):
lo, hi = Fr(0), Fr(1, 4)
for _ in range(64):
    mid = (lo + hi) / 2
    th = theta_at(mid, [Fr(1, 4), Fr(1, 4), Fr(1, 8)])
    if th is not None and th <= Fr(1, 2):
        lo = mid
    else:
        hi = mid
print(f"  kappa needed (coeffs 1/4,1/4,1/8) for theta <= 1/2: kappa ~ {float(lo):.6f}"
      f"   (Macourt supplies kappa = 1/4 = 0.25)")

# needed uniform coeff c (all three sets exponent 1-c... i.e. coeffs (c,c,c)) at kappa=1/4:
lo, hi = Fr(0), Fr(1, 2)
for _ in range(64):
    mid = (lo + hi) / 2
    th = theta_at(Fr(1, 4), [mid, mid, mid])
    if th is not None and th <= Fr(1, 2):
        hi = mid
    else:
        lo = mid
print(f"  uniform residual coeff c needed (kappa=1/4, coeffs (c,c,c)) for theta <= 1/2:"
      f" c ~ {float(hi):.6f}   (Macourt residuals: 1/4, 1/4, 1/8)")

print("\n" + "=" * 78)
print("DICTIONARY: BG chain with PERFECT energies == the pure moment ladder")
print("  (biH shape, perfect t_s = s:  theta(s) = (beta+s-1)/(2s) = momentExponent(s,beta))")
for s in (4, 6, 8, 12, 24, 89):
    th = theta_biH(Fr(4), s, t_perfect(s))
    me = Fr(4 + s - 1, 2 * s)
    print(f"    s={s:3d}: chain theta = {th}   momentExponent = {me}   match = {th == me}")
print("  => the multilinear rounds only TRADE unavailable deep energies for shallow")
print("     proven ones; reaching theta -> 1/2 requires perfect energies at UNBOUNDED")
print("     arity == the open Wick-at-log-depth bound == the wall (dossier v3 sec 2).")

print("\n" + "=" * 78)
print("VERDICT is read off the sweep-B plateau; see header rule.")
print("A-priori kill reminder: `deltaStar_determination_all_or_nothing` (in-tree) makes")
print("ANY fixed power-saving exponent theta > 1/2 irrelevant to delta*; the BG family's")
print("output is always a fixed power law, so attack #5 cannot move delta* even if the")
print("plateau improved -- the probe's numbers quantify how far it is from mattering.")
