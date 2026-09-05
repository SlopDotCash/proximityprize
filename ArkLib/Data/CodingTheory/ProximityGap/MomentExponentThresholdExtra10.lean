import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta=4 gap at the production anchor.**
`θ(89,4) - 1/2 = 3/178` — the gap at the production anchor, restated
from `momentExponent_beta4_r89_gap` in gap-first form. -/
theorem momentExponent_beta4_r89_gap_value :
    momentExponent 89 4 - 1 / 2 = 3 / 178 := by
  rw [momentExponent]
  norm_num

/-- **The beta=4 gap at depth 2.**
`θ(2,4) - 1/2 = 3/4` — above the crossover, the gap is maximal at
shallow depth. -/
theorem momentExponent_beta4_r2_gap :
    momentExponent 2 4 - 1 / 2 = 3 / 4 := by
  rw [momentExponent]
  norm_num

/-- **The beta=4 gap at depth 4.**
`θ(4,4) - 1/2 = 3/8` — halving each time depth doubles. -/
theorem momentExponent_beta4_r4_gap :
    momentExponent 4 4 - 1 / 2 = 3 / 8 := by
  rw [momentExponent]
  norm_num

/-- **The beta=4 gap at depth 8.**
`θ(8,4) - 1/2 = 3/16` — the geometric decay of the gap in depth. -/
theorem momentExponent_beta4_r8_gap :
    momentExponent 8 4 - 1 / 2 = 3 / 16 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r89_gap_value
#print axioms momentExponent_beta4_r2_gap
#print axioms momentExponent_beta4_r4_gap
#print axioms momentExponent_beta4_r8_gap

end ProximityGap.MomentExponentThreshold
