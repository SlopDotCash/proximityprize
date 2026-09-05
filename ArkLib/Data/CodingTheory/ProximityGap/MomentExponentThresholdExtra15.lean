import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 4 depth-128 anchor.**
`θ(128,4) = 131/256` — the production aspect at depth 128, gap `3/256`
(six halvings beyond depth 2). -/
theorem momentExponent_beta4_r128 :
    momentExponent 128 4 = 131 / 256 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-256 anchor.**
`θ(256,4) = 259/512` — the production aspect at depth 256, gap `3/512`
(seven halvings beyond depth 2). -/
theorem momentExponent_beta4_r256 :
    momentExponent 256 4 = 259 / 512 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 2 depth-32 anchor.**
`θ(32,2) = 33/64` — the boundary aspect at depth 32, gap `1/64`. -/
theorem momentExponent_beta2_r32 :
    momentExponent 32 2 = 33 / 64 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 2 depth-64 anchor.**
`θ(64,2) = 65/128` — the boundary aspect at depth 64, gap `1/128`. -/
theorem momentExponent_beta2_r64 :
    momentExponent 64 2 = 65 / 128 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r128
#print axioms momentExponent_beta4_r256
#print axioms momentExponent_beta2_r32
#print axioms momentExponent_beta2_r64

end ProximityGap.MomentExponentThreshold
