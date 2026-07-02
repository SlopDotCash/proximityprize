/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moment-exponent threshold for the pure 2r-th-moment route (#466, dossier v3 §2.5)

Quantifies dossier v3 §2.5: bounding `M = max_{b≠0} |η_b|` via the 2r-th moment
`∑_{b≠0} |η_b|^{2r} ≤ p · E_r`-style counts, with `p ≈ n^β`, yields
`M ≲ n^{θ(r,β)}` where

  `θ(r,β) = momentExponent r β = (β + r − 1) / (2r)`.

Facts proven here (axiom-clean, over `ℝ`; we choose `ℝ` rather than `ℚ` so
the exponent can be compared directly with analytic quantities elsewhere):

* `half_lt_momentExponent`: for `1 ≤ r`, `2 ≤ β`, we have `1/2 < θ(r,β)` —
  the pure moment route ALWAYS overshoots the prize exponent `1/2`; the prize
  `θ = 1/2` is only the unattained `r → ∞` limit.
* `momentExponent_sub_half`: the excess over the prize exponent is *exactly*
  `(β−1)/(2r)` — the route converges to `1/2` only as `r → ∞`, at rate `1/r`.
* `momentExponent_lt_one_iff`: for `0 < r`, `θ(r,β) < 1 ↔ β − 1 < r` —
  non-triviality (beating the trivial `M ≤ n`) requires depth `r > β − 1`,
  which coincides (up to 1) with the DC crossover `r > β` where char-p Wick
  is refuted (`DCEnergyEssential`): the moment route becomes non-trivial only
  in the regime where the char-0 Gaussian moment inputs are unavailable.
* `nontrivial_le_crossover_iff_eq`: for *integer* depths, non-triviality
  (`β − 1 < r`) plus staying at-or-below the DC crossover (`r ≤ β`) holds
  *iff* `r = β` — the non-trivial pre-crossover window is a single rung.
* `momentExponent_strictAnti`: for fixed `β > 2`, `θ(·,β)` is strictly
  decreasing on `r > 0` (proved in full, not just two-point).
* `moment_threshold_beta_four`: at the prize-relevant `β = 4`:
  `θ(3,4) = 1` (r = 3 exactly trivial) and `θ(4,4) = 7/8` (r = 4 first
  non-trivial depth), matching `momentExponent_lt_one_iff` with `β − 1 = 3`.
* `momentExponent_beta4_r89`: at the prize moment depth `r = 89 ≈ ln q`,
  `θ(89,4) = 46/89 ≈ 0.5169` — still strictly above `1/2`.

No axioms, no `sorry`; minimal imports.  Issue #466 (re-landing the dossier-§12 phantom).
-/

set_option autoImplicit false

namespace ProximityGap.MomentExponentThreshold

/-- The exponent `θ(r,β) = (β + r − 1)/(2r)` obtained from the pure
`2r`-th-moment bound with `p ≈ n^β`. -/
noncomputable def momentExponent (r beta : ℝ) : ℝ := (beta + r - 1) / (2 * r)

/-- The pure moment route always yields exponent strictly above `1/2`
(the prize exponent is the unattained `r → ∞` limit). -/
theorem half_lt_momentExponent {r beta : ℝ} (hr : 1 ≤ r) (hb : 2 ≤ beta) :
    1 / 2 < momentExponent r beta := by
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le one_pos hr
  rw [momentExponent, div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The excess of the moment exponent over the prize exponent `1/2` is *exactly*
`(β−1)/(2r)`: the route approaches `1/2` at rate `1/r` and never attains it. -/
theorem momentExponent_sub_half {r beta : ℝ} (hr : 0 < r) :
    momentExponent r beta - 1 / 2 = (beta - 1) / (2 * r) := by
  rw [momentExponent, div_sub_div _ _ (by positivity : (2*r : ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    div_eq_div_iff (by positivity : (0:ℝ) < 2 * r * 2).ne' (by positivity : (0:ℝ) < 2 * r).ne']
  ring

/-- Non-triviality threshold: `θ(r,β) < 1` iff `r > β − 1`. -/
theorem momentExponent_lt_one_iff {r beta : ℝ} (hr : 0 < r) :
    momentExponent r beta < 1 ↔ beta - 1 < r := by
  rw [momentExponent, div_lt_one (by positivity)]
  constructor <;> intro h <;> linarith

/-- For fixed `β > 2`, the exponent is strictly decreasing in `r` on `r > 0`. -/
theorem momentExponent_strictAnti {beta r₁ r₂ : ℝ} (hb : 2 < beta)
    (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    momentExponent r₂ beta < momentExponent r₁ beta := by
  have h2 : 0 < r₂ := lt_trans h1 h12
  rw [momentExponent, momentExponent,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The one-rung window.** For integer depths, non-triviality (`β − 1 < r`) together
with staying at-or-below the DC crossover (`r ≤ β`) holds *iff* `r = β`: the moment route
has exactly one integer depth that is non-trivial and not already past the refuted
raw-Wick regime. -/
theorem nontrivial_le_crossover_iff_eq {r beta : ℕ} :
    ((beta : ℝ) - 1 < (r : ℝ) ∧ (r : ℝ) ≤ (beta : ℝ)) ↔ r = beta := by
  constructor
  · rintro ⟨h1, h2⟩
    have hb : beta < r + 1 := by
      have : (beta : ℝ) < (r : ℝ) + 1 := by linarith
      exact_mod_cast this
    have hr : r ≤ beta := by exact_mod_cast h2
    omega
  · rintro rfl
    exact ⟨by linarith, le_refl _⟩

/-- Prize-relevant slice `β = 4`: `θ(3,4) = 1` and `θ(4,4) = 7/8`. -/
theorem moment_threshold_beta_four :
    momentExponent 3 4 = 1 ∧ momentExponent 4 4 = 7/8 := by
  constructor <;> · rw [momentExponent]; norm_num

/-- Prize-diagonal anchor at the prize moment depth `r = 89 ≈ ln q`:
`θ(89,4) = 46/89 ≈ 0.5169` — still strictly above `1/2`. -/
theorem momentExponent_beta4_r89 : momentExponent 89 4 = 46 / 89 := by
  rw [momentExponent]; norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms half_lt_momentExponent
#print axioms momentExponent_sub_half
#print axioms momentExponent_lt_one_iff
#print axioms momentExponent_strictAnti
#print axioms nontrivial_le_crossover_iff_eq
#print axioms moment_threshold_beta_four
#print axioms momentExponent_beta4_r89

end ProximityGap.MomentExponentThreshold
