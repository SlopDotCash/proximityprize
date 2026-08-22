import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 4 depth-3 anchor.**
`θ(3,4) = 1` — the exact crossover depth for the production aspect,
restated as an anchor (equals `momentExponent_beta4_crossover`). -/
theorem momentExponent_beta4_r3_anchor :
    momentExponent 3 4 = 1 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-5 anchor.**
`θ(5,4) = 4/5` — the first depth strictly inside the window below the
crossover. -/
theorem momentExponent_beta4_r5 :
    momentExponent 5 4 = 4 / 5 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-6 anchor.**
`θ(6,4) = 3/4` — inside the window at moderate depth. -/
theorem momentExponent_beta4_r6 :
    momentExponent 6 4 = 3 / 4 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-10 anchor.**
`θ(10,4) = 13/20` — inside the window at depth 10. -/
theorem momentExponent_beta4_r10 :
    momentExponent 10 4 = 13 / 20 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r3_anchor
#print axioms momentExponent_beta4_r5
#print axioms momentExponent_beta4_r6
#print axioms momentExponent_beta4_r10

end ProximityGap.MomentExponentThreshold
