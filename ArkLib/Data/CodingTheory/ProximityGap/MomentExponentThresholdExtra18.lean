import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 4 gap at depth 3 is exactly half.**
`θ(3,4) - 1/2 = 1/2` — at the crossover depth the gap equals the prize
half, the boundary of the production window. -/
theorem momentExponent_beta4_r3_gap :
    momentExponent 3 4 - 1 / 2 = 1 / 2 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 gap at depth 5.**
`θ(5,4) - 1/2 = 3/10` — inside the window, gap shrinks below the half. -/
theorem momentExponent_beta4_r5_gap :
    momentExponent 5 4 - 1 / 2 = 3 / 10 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 gap at depth 10.**
`θ(10,4) - 1/2 = 3/20` — further inside the window. -/
theorem momentExponent_beta4_r10_gap :
    momentExponent 10 4 - 1 / 2 = 3 / 20 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 gap at depth 20.**
`θ(20,4) - 1/2 = 3/40` — the gap halves each time depth doubles past
the crossover. -/
theorem momentExponent_beta4_r20_gap :
    momentExponent 20 4 - 1 / 2 = 3 / 40 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r3_gap
#print axioms momentExponent_beta4_r5_gap
#print axioms momentExponent_beta4_r10_gap
#print axioms momentExponent_beta4_r20_gap

end ProximityGap.MomentExponentThreshold
