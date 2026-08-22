import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The gap stays positive for every depth at β ≥ 2.**
`0 < θ(r,β) - 1/2` for `0 < r` and `2 ≤ β` — the gap persists across
the whole `β ≥ 2` regime, complementing `half_lt_momentExponent`. -/
theorem momentExponent_gap_pos_of_two_le {r beta : ℝ} (hr : 0 < r)
    (hb : 2 ≤ beta) :
    0 < momentExponent r beta - 1 / 2 := by
  rw [momentExponent_sub_half hr]
  have hden : (0 : ℝ) < 2 * r := by positivity
  have hnum : 0 < beta - 1 := by linarith
  exact div_pos hnum hden

/-- **The gap is at most (β-1)/2 at unit depth.**
`θ(r,β) - 1/2 ≤ (β-1)/2` for `1 ≤ r` — the depth-1 gap is the maximal
one; deeper depths shrink it. -/
theorem momentExponent_gap_le_unit {r beta : ℝ} (hr : 1 ≤ r) (hb : 1 ≤ beta) :
    momentExponent r beta - 1 / 2 ≤ (beta - 1) / 2 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < r)]
  have hden : (0 : ℝ) < 2 * r := by positivity
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
  have hnonneg : 0 ≤ beta - 1 := by linarith
  nlinarith

/-- **The gap is strictly decreasing in depth (β ≥ 2).**
For `0 < r₁ < r₂` and `β ≥ 2`, `θ(r₂,β) - 1/2 < θ(r₁,β) - 1/2` — the
strict depth monotonicity of the gap in the `β ≥ 2` regime. -/
theorem momentExponent_gap_strictAnti_two_le {beta r₁ r₂ : ℝ}
    (hb : 2 ≤ beta) (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    momentExponent r₂ beta - 1 / 2 < momentExponent r₁ beta - 1 / 2 := by
  have h2 : 0 < r₂ := lt_trans h1 h12
  rw [momentExponent_sub_half h2, momentExponent_sub_half h1]
  have hnum : 0 < beta - 1 := by linarith
  have hden1 : (0 : ℝ) < 2 * r₁ := by positivity
  have hden2 : (0 : ℝ) < 2 * r₂ := by positivity
  rw [div_lt_div_iff₀ hden2 hden1]
  nlinarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_gap_pos_of_two_le
#print axioms momentExponent_gap_le_unit
#print axioms momentExponent_gap_strictAnti_two_le

end ProximityGap.MomentExponentThreshold
