import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 5 anchor.**
At aspect 5 the exponent is `θ(r,5) = (r+4)/(2r)` — the closed form
above the production aspect 4, deeper into the over-trivial regime. -/
theorem momentExponent_beta5 {r : ℝ} :
    momentExponent r 5 = (r + 4) / (2 * r) := by
  rw [momentExponent]
  ring

/-- **The beta = 6 anchor.**
At aspect 6 the exponent is `θ(r,6) = (r+5)/(2r)` — further into the
over-trivial regime. -/
theorem momentExponent_beta6 {r : ℝ} :
    momentExponent r 6 = (r + 5) / (2 * r) := by
  rw [momentExponent]
  ring

/-- **The beta = 4 depth-16 anchor.**
`θ(16,4) = 19/32` — the production aspect at depth 16, gap `3/32`
(three halvings beyond depth 2). -/
theorem momentExponent_beta4_r16 :
    momentExponent 16 4 = 19 / 32 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-32 anchor.**
`θ(32,4) = 35/64` — the production aspect at depth 32, gap `3/64`
(four halvings beyond depth 2). -/
theorem momentExponent_beta4_r32 :
    momentExponent 32 4 = 35 / 64 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta5
#print axioms momentExponent_beta6
#print axioms momentExponent_beta4_r16
#print axioms momentExponent_beta4_r32

end ProximityGap.MomentExponentThreshold
