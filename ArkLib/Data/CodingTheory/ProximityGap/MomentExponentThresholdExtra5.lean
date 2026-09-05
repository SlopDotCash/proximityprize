import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The r = 1 boundary anchor.**
At the shallowest positive depth, `θ(1,β) = (β+1-1)/(2·1) = β/2`. This is
the largest exponent attainable at unit depth — the trivial-ward extreme
of the depth ladder. -/
theorem momentExponent_r1 {beta : ℝ} :
    momentExponent 1 beta = beta / 2 := by
  rw [momentExponent]
  ring

/-- **The r = 1 boundary gap.**
At unit depth, `θ(1,β) - 1/2 = (β-1)/2`, growing linearly in β — the
maximal gap-to-prize at the shallowest depth. -/
theorem momentExponent_r1_gap {beta : ℝ} :
    momentExponent 1 beta - 1 / 2 = (beta - 1) / 2 := by
  rw [momentExponent_sub_half (by norm_num : (0 : ℝ) < 1)]
  ring

/-- **The beta = 4 anchor family at the shallow end.**
`θ(1,4) = 2`: at unit depth and aspect 4 the exponent is far above the
trivial ceiling — the depth-1 extreme of the β=4 ladder. -/
theorem momentExponent_beta4_r1 :
    momentExponent 1 4 = 2 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-two anchor.**
`θ(2,4) = 5/4` — still above 1, matching `momentExponent_beta2`-style
boundary behavior at the first non-trivial depth below the crossover. -/
theorem momentExponent_beta4_r2 :
    momentExponent 2 4 = 5 / 4 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_r1
#print axioms momentExponent_r1_gap
#print axioms momentExponent_beta4_r1
#print axioms momentExponent_beta4_r2

end ProximityGap.MomentExponentThreshold
