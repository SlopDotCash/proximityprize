/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The ensemble ramp-defect law for the Jacobi recurrence of the η-spectrum (#466, lane R4)

Round-1 P4 (`probe_466_hankel_turnover.py`) measured, for the empirical spectral measure of the
Gauss periods `{η_b : b ≠ 0}` (`η_b = Σ_{x∈μ_n} e_p(bx)`, real since `-1 ∈ μ_n` for even `n`),
that the first Jacobi ramp defect is `1 - q_1 = (n-1)/(p-1) + n/(p-1)²` exact to `~1e-13`,
where `q_j = b_j²/(nj)` and `b_j` is the `j`-th Jacobi (three-term-recurrence) off-diagonal.
This file PROVES that law and the `j = 2` analogue as exact field-arithmetic identities from
the moment inputs, which are themselves exact counting identities:

* `M_1 = -n/(p-1)`   — from `Σ_{all b} η_b = 0` (`0 ∉ μ_n`; unconditional);
* `M_2 = n(p-n)/(p-1)` — Parseval `Σ_{b≠0} η_b² = n(p-n)` (unconditional; the in-tree
  transported form is `subgroup_gaussSum_secondMoment` in `SubgroupGaussSumSecondMoment.lean`);
* `M_3 = -n³/(p-1)`  — CLEAN hypothesis `T_3 = 0` (no additive triples `x+y+z=0` in `μ_n`;
  `Σ_{all b} η_b³ = p·T_3` exactly);
* `M_4 = ((3n²-3n)p - n⁴)/(p-1)` — CLEAN hypothesis `E_2 = 3n²-3n` (the even-`n` char-0
  additive energy; generic prime, cf. the `Fermat257EnergyCrossover` anomaly context).

The measure is neither centered (`M_1 ≠ 0`) nor even (skewness `c_3 = O(n³/p) ≠ 0`), so the
true Jacobi coefficients are `b_1² = c_2` and `b_2² = c_4/c_2 - (c_3/c_2)² - c_2` with `c_k`
the CENTRAL moments — the mean- and skewness-corrections are exactly what round-1's measured
`n/(p-1)²` term is.

## The laws (proved below; symbolically re-derived and numerically validated to float precision
## in `scripts/probes/probe_466_jacobi_ramp_defect.py` → `_out_466_jacobi_ramp_defect.txt`)

* j = 1 (`oneMinusQ1_exact`, UNCONDITIONAL inputs):
  `b_1² = np(p-1-n)/(p-1)²` and `1 - b_1²/n = (n-1)/(p-1) + n/(p-1)²`.
* j = 1 raw variant (`oneMinusQ1_raw`): `1 - M_2/n = (n-1)/(p-1)` (pure Parseval, no mean
  correction — the `n/(p-1)²` gap between the two is the mean-square `M_1²/n`).
* j = 2 (`b2sq_closed` / `oneMinusQ2_exact`, CONDITIONAL on the clean energies):
  `b_2² = (p-1)((2n-3)p - (n³-3))/(p-1-n)²` and
  `1 - q_2 = (3(p-1)² - 4n²(p-1) - 2n(p-1) + n³(p+1)) / (2n(p-1-n)²)`.
* Floor split (`oneMinusQ2_exceeds_floor`):
  `1 - q_2 = 3/(2n) + ((n-2)²(p-1) + n(2n-3)) / (2(p-1-n)²)` — the j = 2 defect carries the
  char-0 Bessel floor `3/(2n)` (the `-3n` in `E_2`, which reads `n` only) PLUS an explicitly
  positive `p`-ramp `≈ (n-2)²/(2(p-1))`; contrast j = 1 whose defect reads `p` only.

## HONESTY (part (d) of the lane)

These identities pin the ensemble MEAN ramp only (j = 1, 2 of the Jacobi recurrence of the
FULL spectral measure — equivalently the first two Hankel determinants, i.e. moments up to
`E_2`). Round-1 P4 showed the Hankel/Jacobi window reads `p`, not the instance: the worst-case
turnover `k*(instance)`, everything at depth `j ≥ 3` (which requires `E_3, E_4, …` where the
char-p defect lives), and the prize-relevant worst-`b` sup-norm question all stay OPEN. This
brick is exact bookkeeping at the shallow end, NOT progress on the wall. The clean-energy
hypotheses (`T_3 = 0`, `E_2 = 3n²-3n`) are named inputs — generically true, false at anomalous
primes (in-tree crossover context), and NOT discharged here. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw

/-! ## j = 1: the ramp-defect law from the mean + Parseval inputs (unconditional inputs) -/

/-- Raw Parseval variant (no mean correction): `1 - M_2/n = (n-1)/(p-1)`. -/
theorem oneMinusQ1_raw (n p m2 : ℝ) (hn : n ≠ 0) (hp : p ≠ 1)
    (hm2 : m2 = n * (p - n) / (p - 1)) :
    1 - m2 / n = (n - 1) / (p - 1) := by
  have hP : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  subst hm2
  field_simp
  ring

/-- Closed form of the first Jacobi off-diagonal: `b_1² = c_2 = M_2 - M_1² = np(p-1-n)/(p-1)²`.
Inputs: the mean identity `M_1 = -n/(p-1)` and Parseval `M_2 = n(p-n)/(p-1)` — both exact
counting identities for every proper subgroup `μ_n ⊂ F_p^×`. -/
theorem b1sq_closed (n p m1 m2 b1sq : ℝ) (hp : p ≠ 1)
    (hm1 : m1 = -n / (p - 1)) (hm2 : m2 = n * (p - n) / (p - 1))
    (hb1 : b1sq = m2 - m1 ^ 2) :
    b1sq = n * p * (p - 1 - n) / (p - 1) ^ 2 := by
  have hP : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  subst hm1 hm2 hb1
  field_simp
  ring

/-- **The j = 1 ensemble ramp-defect law** (round-1's measured law, now exact):
`1 - q_1 = 1 - b_1²/n = (n-1)/(p-1) + n/(p-1)²`.  The second term is the mean-square
correction `M_1²/n` — the Jacobi recurrence auto-centers the measure. -/
theorem oneMinusQ1_exact (n p m1 m2 b1sq : ℝ) (hn : n ≠ 0) (hp : p ≠ 1)
    (hm1 : m1 = -n / (p - 1)) (hm2 : m2 = n * (p - n) / (p - 1))
    (hb1 : b1sq = m2 - m1 ^ 2) :
    1 - b1sq / n = (n - 1) / (p - 1) + n / (p - 1) ^ 2 := by
  have hP : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  subst hm1 hm2 hb1
  field_simp
  ring

/-! ## j = 2: the ramp-defect law CONDITIONAL on the clean energies `T_3 = 0`, `E_2 = 3n²-3n` -/

/-- Closed form of the second Jacobi off-diagonal from the general (mean- and skewness-aware)
Jacobi formula `b_2² = c_4/c_2 - (c_3/c_2)² - c_2` in central moments, with the four raw-moment
inputs.  `hm3`/`hm4` are the CLEAN-regime hypotheses (`T_3 = 0`, `E_2 = 3n²-3n`); the result is
`b_2² = (p-1)((2n-3)p - (n³-3))/(p-1-n)²`. -/
theorem b2sq_closed (n p m1 m2 m3 m4 c2 c3 c4 b2sq : ℝ)
    (hn : 0 < n) (hp : 1 < p) (hnp : n < p - 1)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hb2 : b2sq = c4 / c2 - (c3 / c2) ^ 2 - c2) :
    b2sq = (p - 1) * ((2 * n - 3) * p - (n ^ 3 - 3)) / (p - 1 - n) ^ 2 := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hP0 : (0 : ℝ) < p - 1 := by linarith
  have hQ0 : (0 : ℝ) < p - 1 - n := by linarith
  have hP : p - 1 ≠ 0 := ne_of_gt hP0
  have hQ : p - 1 - n ≠ 0 := ne_of_gt hQ0
  have hn' : n ≠ 0 := ne_of_gt hn
  subst hm1 hm2 hm3 hm4
  -- the variance in closed form, and its nonvanishing (this is where `n < p - 1` is used)
  have hc2v : c2 = n * p * (p - 1 - n) / (p - 1) ^ 2 := by
    rw [hc2]; field_simp; ring
  have hc2pos : 0 < c2 := by
    rw [hc2v]
    exact div_pos (mul_pos (mul_pos hn hp0) hQ0) (pow_pos hP0 2)
  have hc2ne : c2 ≠ 0 := ne_of_gt hc2pos
  -- clear the division by the variance while it is still an atom
  have key : b2sq * c2 ^ 2 = c4 * c2 - c3 ^ 2 - c2 ^ 3 := by
    rw [hb2]; field_simp
  -- substitute the explicit central moments and normalize
  have main : c4 * c2 - c3 ^ 2 - c2 ^ 3
      = (p - 1) * ((2 * n - 3) * p - (n ^ 3 - 3)) / (p - 1 - n) ^ 2 * c2 ^ 2 := by
    rw [hc3, hc4, hc2v]
    field_simp
    ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hc2ne) (key.trans main)

/-- **The j = 2 ensemble ramp-defect law** (clean regime):
`1 - q_2 = 1 - b_2²/(2n) = (3(p-1)² - 4n²(p-1) - 2n(p-1) + n³(p+1)) / (2n(p-1-n)²)`.
Leading behaviour `3/(2n) + (n²/2 - 2n + 2)/(p-1) + O(1/(p-1)²)`: unlike j = 1 (which reads
`p` only), the j = 2 defect has an `n`-floor coming from the `-3n` in the clean `E_2`. -/
theorem oneMinusQ2_exact (n p m1 m2 m3 m4 c2 c3 c4 b2sq : ℝ)
    (hn : 0 < n) (hp : 1 < p) (hnp : n < p - 1)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hb2 : b2sq = c4 / c2 - (c3 / c2) ^ 2 - c2) :
    1 - b2sq / (2 * n)
      = (3 * (p - 1) ^ 2 - 4 * n ^ 2 * (p - 1) - 2 * n * (p - 1) + n ^ 3 * (p + 1))
        / (2 * n * (p - 1 - n) ^ 2) := by
  have hb2v := b2sq_closed n p m1 m2 m3 m4 c2 c3 c4 b2sq hn hp hnp
    hm1 hm2 hm3 hm4 hc2 hc3 hc4 hb2
  have hQ : p - 1 - n ≠ 0 := by
    have : (0 : ℝ) < p - 1 - n := by linarith
    exact ne_of_gt this
  have hn' : n ≠ 0 := ne_of_gt hn
  rw [hb2v]
  field_simp
  ring

/-- **Floor split**: `1 - q_2 = 3/(2n) + ((n-2)²(p-1) + n(2n-3)) / (2(p-1-n)²)`.
The j = 2 ramp defect is EXACTLY the char-0 Bessel floor `3/(2n)` (present for every `p`;
it is the `-3n` of `E_2 = 3n² - 3n`) plus an explicitly nonnegative `p`-ramp
`≈ (n-2)²/(2(p-1))`.  So the shallow Jacobi window separates: `j = 1` reads `p` only,
`j = 2` reads `n` at leading order and `p` in the ramp. -/
theorem oneMinusQ2_exceeds_floor (n p m1 m2 m3 m4 c2 c3 c4 b2sq : ℝ)
    (hn : 0 < n) (hp : 1 < p) (hnp : n < p - 1)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hb2 : b2sq = c4 / c2 - (c3 / c2) ^ 2 - c2) :
    1 - b2sq / (2 * n)
      = 3 / (2 * n) + ((n - 2) ^ 2 * (p - 1) + n * (2 * n - 3)) / (2 * (p - 1 - n) ^ 2) := by
  have h := oneMinusQ2_exact n p m1 m2 m3 m4 c2 c3 c4 b2sq hn hp hnp
    hm1 hm2 hm3 hm4 hc2 hc3 hc4 hb2
  rw [h]
  have hQ : p - 1 - n ≠ 0 := by
    have : (0 : ℝ) < p - 1 - n := by linarith
    exact ne_of_gt this
  have hn' : n ≠ 0 := ne_of_gt hn
  field_simp
  ring

end ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.oneMinusQ1_raw
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.b1sq_closed
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.oneMinusQ1_exact
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.b2sq_closed
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.oneMinusQ2_exact
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLaw.oneMinusQ2_exceeds_floor
