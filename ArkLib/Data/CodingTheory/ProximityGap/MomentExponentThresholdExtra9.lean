import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The depth-2 anchor for β = 2.**
`θ(2,2) = 3/4` — at the aspect-2 boundary and shallow depth, the
exponent sits at the quarter-point above the prize floor. -/
theorem momentExponent_beta2_r2 :
    momentExponent 2 2 = 3 / 4 := by
  rw [momentExponent]
  norm_num

/-- **The depth-4 anchor for β = 2.**
`θ(4,2) = 5/8` — the boundary aspect at moderate depth, still above
`1/2`. -/
theorem momentExponent_beta2_r4 :
    momentExponent 4 2 = 5 / 8 := by
  rw [momentExponent]
  norm_num

/-- **The depth-8 anchor for β = 2.**
`θ(8,2) = 9/16` — the boundary aspect at depth 8, asymptotically
approaching `1/2`. -/
theorem momentExponent_beta2_r8 :
    momentExponent 8 2 = 9 / 16 := by
  rw [momentExponent]
  norm_num

/-- **The depth-16 anchor for β = 2.**
`θ(16,2) = 17/32` — the boundary aspect at depth 16, one ULP-region
closer to the prize floor. -/
theorem momentExponent_beta2_r16 :
    momentExponent 16 2 = 17 / 32 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta2_r2
#print axioms momentExponent_beta2_r4
#print axioms momentExponent_beta2_r8
#print axioms momentExponent_beta2_r16

end ProximityGap.MomentExponentThreshold
