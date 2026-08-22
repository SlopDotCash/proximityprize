import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 3 boundary anchor.**
At aspect 3 the exponent is `θ(r,3) = (r+2)/(2r)` — the closed form for
the middle of the aspect ladder, between the `β = 2` and `β = 4`
anchors. -/
theorem momentExponent_beta3 {r : ℝ} :
    momentExponent r 3 = (r + 2) / (2 * r) := by
  rw [momentExponent]
  ring

/-- **The beta = 4 crossover depth.**
The `r = β - 1 = 3` crossover at production aspect: `θ(3,4) = 1` exactly.
This pins the trivial-ceiling boundary depth for the β=4 ladder. -/
theorem momentExponent_beta4_crossover :
    momentExponent 3 4 = 1 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-four anchor.**
`θ(4,4) = 7/8` — below the trivial ceiling but still above the prize
floor `1/2`, inside the production window. -/
theorem momentExponent_beta4_r4 :
    momentExponent 4 4 = 7 / 8 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-eight anchor.**
`θ(8,4) = 11/16` — deeper into the window, asymptotically approaching
`1/2` from above as depth grows. -/
theorem momentExponent_beta4_r8 :
    momentExponent 8 4 = 11 / 16 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta3
#print axioms momentExponent_beta4_crossover
#print axioms momentExponent_beta4_r4
#print axioms momentExponent_beta4_r8

end ProximityGap.MomentExponentThreshold
