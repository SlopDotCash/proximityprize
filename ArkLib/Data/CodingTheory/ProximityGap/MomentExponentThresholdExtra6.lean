import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The gap is positive exactly inside the nontrivial window.**
`θ(r,β) - 1/2 > 0` iff `β > 1` — the prize-floor comparison in closed
form. Complements `momentExponent_one_sub_pos` (gap to the trivial
ceiling). -/
theorem momentExponent_gap_pos_iff {r beta : ℝ} (hr : 0 < r) :
    0 < momentExponent r beta - 1 / 2 ↔ 1 < beta := by
  rw [momentExponent_sub_half hr]
  constructor
  · intro hpos
    have hden : (0 : ℝ) < 2 * r := by positivity
    have hlt := (div_pos_iff_of_pos_right hden).mp hpos
    nlinarith
  · intro hb
    have hden : (0 : ℝ) < 2 * r := by positivity
    have hnum : 0 < beta - 1 := by linarith
    exact div_pos hnum hden

/-- **The r = β - 1 crossover gap.**
At the crossover `r = β - 1` the exponent is exactly `1/2 + 1/2 = 1`:
`θ(r,β) - 1/2 = 1/2` — the trivial-ceiling boundary in gap terms. -/
theorem momentExponent_crossover_gap {beta r : ℝ} (hr : 0 < r)
    (hcross : r = beta - 1) :
    momentExponent r beta - 1 / 2 = 1 / 2 := by
  rw [momentExponent_sub_half hr, hcross]
  have hb : (beta - 1 : ℝ) ≠ 0 := by
    intro h
    have : (r : ℝ) = 0 := by simpa [hcross] using h
    linarith
  field_simp [hb]

/-- **Monotone depth shrinks the gap.**
For fixed `β > 1`, `θ(r,β) - 1/2` is strictly decreasing in `r` — the
gap-to-prize version of `momentExponent_strictAnti_of_one_le`. -/
theorem momentExponent_gap_strictAnti {beta r₁ r₂ : ℝ} (hb : 1 < beta)
    (h1 : 0 < r₁) (h12 : r₁ < r₂) :
    momentExponent r₂ beta - 1 / 2 < momentExponent r₁ beta - 1 / 2 := by
  have h2 : 0 < r₂ := lt_trans h1 h12
  rw [momentExponent_sub_half h2, momentExponent_sub_half h1]
  have hnum : 0 < beta - 1 := by linarith
  have hden1 : (0 : ℝ) < 2 * r₁ := by positivity
  have hden2 : (0 : ℝ) < 2 * r₂ := by positivity
  have hlt : (2 * r₁ : ℝ) < 2 * r₂ := by nlinarith
  -- (beta-1)/(2*r₂) < (beta-1)/(2*r₁): multiply through by positive
  -- denominators; the claim reduces to 2*r₁ < 2*r₂.
  rw [div_lt_div_iff₀ hden2 hden1]
  nlinarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_gap_pos_iff
#print axioms momentExponent_crossover_gap
#print axioms momentExponent_gap_strictAnti

end ProximityGap.MomentExponentThreshold
