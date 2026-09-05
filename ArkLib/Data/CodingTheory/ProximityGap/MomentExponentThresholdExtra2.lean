import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- For fixed `β > 1`, the exponent is strictly decreasing in `r` on `r > 0`
even without the `2 < β` hypothesis: the derivative sign only needs
`β > 1`. Complements `momentExponent_strictAnti` (which requires `2 < β`). -/
theorem momentExponent_strictAnti_of_one_le {beta r₁ r₂ : ℝ} (hb : 1 < beta)
    (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    momentExponent r₂ beta < momentExponent r₁ beta := by
  have h2 : 0 < r₂ := lt_trans h1 h12
  rw [momentExponent, momentExponent]
  have hpos₁ : (0 : ℝ) < 2 * r₁ := by positivity
  have hpos₂ : (0 : ℝ) < 2 * r₂ := by positivity
  rw [div_lt_div_iff₀ hpos₂ hpos₁]
  nlinarith

/-- At every fixed `β > 1`, the moment exponent stays strictly above `1/2`
for all finite depths — the approach to the prize exponent is asymptotic. -/
theorem momentExponent_ge_half_of_one_le {r beta : ℝ} (hr : 0 < r) (hb : 1 < beta) :
    1 / 2 < momentExponent r beta := by
  rw [momentExponent, div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) (by positivity)]
  nlinarith

/-- The gap to the prize exponent `θ - 1/2 = (β-1)/(2r)` is strictly
decreasing in `r` and vanishes in the limit — the quantitative form of the
"unattained limit" statement. -/
theorem momentExponent_gap_strictAnti {beta r₁ r₂ : ℝ} (hb : 1 < beta)
    (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    momentExponent r₂ beta - 1 / 2 < momentExponent r₁ beta - 1 / 2 := by
  have h2 : 0 < r₂ := lt_trans h1 h12
  rw [momentExponent_sub_half h2, momentExponent_sub_half h1]
  have hpos₁ : (0 : ℝ) < 2 * r₁ := by positivity
  have hpos₂ : (0 : ℝ) < 2 * r₂ := by positivity
  rw [div_lt_div_iff₀ hpos₂ hpos₁]
  nlinarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_strictAnti_of_one_le
#print axioms momentExponent_ge_half_of_one_le
#print axioms momentExponent_gap_strictAnti

end ProximityGap.MomentExponentThreshold
