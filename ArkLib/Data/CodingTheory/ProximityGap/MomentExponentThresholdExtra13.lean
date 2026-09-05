import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The gap is exactly (β-1)/(2r).**
Restates `momentExponent_sub_half` with the gap on the left: for `0 < r`,
`θ(r,β) - 1/2 = (β-1)/(2r)`. -/
theorem momentExponent_gap_eq {r beta : ℝ} (hr : 0 < r) :
    momentExponent r beta - 1 / 2 = (beta - 1) / (2 * r) := by
  rw [momentExponent_sub_half hr]

/-- **The depth-1 gap at aspect β.**
`θ(1,β) - 1/2 = (β-1)/2` — the maximal gap at unit depth, restated in
gap-first form. -/
theorem momentExponent_r1_gap_value {beta : ℝ} :
    momentExponent 1 beta - 1 / 2 = (beta - 1) / 2 := by
  rw [momentExponent_sub_half (by norm_num : (0 : ℝ) < 1)]
  ring

/-- **The gap is proportional to β - 1.**
For fixed `r`, doubling `β - 1` doubles the gap:
`θ(r, 2β-1) - 1/2 = 2·(θ(r,β) - 1/2)` when `0 < r`. -/
theorem momentExponent_gap_double_beta {r beta : ℝ} (hr : 0 < r) :
    momentExponent r (2 * beta - 1) - 1 / 2 =
      2 * (momentExponent r beta - 1 / 2) := by
  rw [momentExponent_sub_half hr, momentExponent_sub_half hr]
  field_simp
  ring

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_gap_eq
#print axioms momentExponent_r1_gap_value
#print axioms momentExponent_gap_double_beta

end ProximityGap.MomentExponentThreshold
