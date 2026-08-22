import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 4 depth-3 gap is maximal in the window.**
For every depth `3 ≤ r`, `θ(r,4) - 1/2 ≤ 1/2` — the crossover depth
carries the largest gap inside the window. -/
theorem momentExponent_beta4_gap_le_half {r : ℝ} (hr : 3 ≤ r) :
    momentExponent r 4 - 1 / 2 ≤ 1 / 2 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < r)]
  have hden : (0 : ℝ) < 2 * r := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- **The beta = 4 gap is below 3/10 for depth ≥ 5.**
For every depth `5 ≤ r`, `θ(r,4) - 1/2 ≤ 3/10` — the window shrinks
past depth 5. -/
theorem momentExponent_beta4_gap_le_three_tenths {r : ℝ} (hr : 5 ≤ r) :
    momentExponent r 4 - 1 / 2 ≤ 3 / 10 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < r)]
  have hden : (0 : ℝ) < 2 * r := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- **The beta = 4 gap is below 1/8 for depth ≥ 12.**
For every depth `12 ≤ r`, `θ(r,4) - 1/2 ≤ 1/8` — the window tightens
with depth. -/
theorem momentExponent_beta4_gap_le_eighth {r : ℝ} (hr : 12 ≤ r) :
    momentExponent r 4 - 1 / 2 ≤ 1 / 8 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < r)]
  have hden : (0 : ℝ) < 2 * r := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_gap_le_half
#print axioms momentExponent_beta4_gap_le_three_tenths
#print axioms momentExponent_beta4_gap_le_eighth

end ProximityGap.MomentExponentThreshold
