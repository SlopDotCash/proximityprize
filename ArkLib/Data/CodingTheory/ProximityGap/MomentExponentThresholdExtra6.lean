import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The exponent is above the prize floor exactly when β > 1.**
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

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_gap_pos_iff
#print axioms momentExponent_crossover_gap

end ProximityGap.MomentExponentThreshold
