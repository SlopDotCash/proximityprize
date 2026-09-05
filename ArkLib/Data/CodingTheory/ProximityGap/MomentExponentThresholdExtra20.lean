import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The beta = 4 depth-40 anchor.**
`θ(40,4) = 43/80` — the production aspect at depth 40, gap `3/80`. -/
theorem momentExponent_beta4_r40 :
    momentExponent 40 4 = 43 / 80 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-80 anchor.**
`θ(80,4) = 83/160` — the production aspect at depth 80, gap `3/160`. -/
theorem momentExponent_beta4_r80 :
    momentExponent 80 4 = 83 / 160 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-160 anchor.**
`θ(160,4) = 163/320` — the production aspect at depth 160, gap `3/320`. -/
theorem momentExponent_beta4_r160 :
    momentExponent 160 4 = 163 / 320 := by
  rw [momentExponent]
  norm_num

/-- **The beta = 4 depth-320 anchor.**
`θ(320,4) = 323/640` — the production aspect at depth 320, gap `3/640`. -/
theorem momentExponent_beta4_r320 :
    momentExponent 320 4 = 323 / 640 := by
  rw [momentExponent]
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r40
#print axioms momentExponent_beta4_r80
#print axioms momentExponent_beta4_r160
#print axioms momentExponent_beta4_r320

end ProximityGap.MomentExponentThreshold
