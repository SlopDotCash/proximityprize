import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The gap halves when depth doubles.**
`θ(2r,4) - 1/2 = (θ(r,4) - 1/2)/2` — the geometric decay of the β=4
gap in depth, in closed form. -/
theorem momentExponent_beta4_gap_halving {r : ℝ} (hr : 0 < r) :
    momentExponent (2 * r) 4 - 1 / 2 = (momentExponent r 4 - 1 / 2) / 2 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < 2 * r),
      momentExponent_sub_half hr]
  field_simp

/-- **The gap at depth 4 is a quarter of the depth-1 gap.**
`θ(4,4) - 1/2 = (θ(1,4) - 1/2)/4` — two halvings from unit depth. -/
theorem momentExponent_beta4_gap_quarter :
    momentExponent 4 4 - 1 / 2 = (momentExponent 1 4 - 1 / 2) / 4 := by
  rw [momentExponent_sub_half (by norm_num : (0 : ℝ) < 4),
      momentExponent_sub_half (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- **The depth-64 anchor for β = 4.**
`θ(64,4) = 67/128` — the gap `3/128` at depth 64, six halvings from the
depth-1 gap `3/2`. -/
theorem momentExponent_beta4_r64 :
    momentExponent 64 4 = 67 / 128 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_gap_halving
#print axioms momentExponent_beta4_gap_quarter
#print axioms momentExponent_beta4_r64

end ProximityGap.MomentExponentThreshold
