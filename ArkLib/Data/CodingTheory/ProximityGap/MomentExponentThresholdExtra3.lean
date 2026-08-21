import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The prize-diagonal anchor expressed through the triviality gap.**
At the production anchor `(r, β) = (89, 4)`, the complementary gap to
triviality is `1 - θ(89,4) = 43/89`. Combined with
`momentExponent_beta4_r89` (`θ = 46/89`) this pins the full distance
picture: `46/89` above the prize floor `1/2`, `43/89` below the trivial
ceiling `1`. -/
theorem momentExponent_beta4_r89_one_sub :
    1 - momentExponent 89 4 = 43 / 89 := by
  rw [momentExponent]; norm_num

/-- **The triviality ceiling in closed form.**
`1 - θ(r,β) = (r - (β-1)) / (2r)` is never negative for `r ≥ β - 1` and
strictly positive above the crossover — the nontriviality region in gap
terms. -/
theorem momentExponent_one_sub_nonneg {r beta : ℝ} (hr : 0 < r)
    (hge : beta - 1 ≤ r) :
    0 ≤ 1 - momentExponent r beta := by
  rw [momentExponent]
  have hden : (2 * r : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  have hnum : 0 ≤ 2 * r - (beta + r - 1) := by nlinarith
  nlinarith

/-- **Strictly inside the nontrivial window.**
For `β - 1 < r` the gap to triviality is strictly positive — the exponent
is genuinely below the ceiling, the regime the δ* campaign operates in. -/
theorem momentExponent_one_sub_pos {r beta : ℝ} (hr : 0 < r)
    (hgt : beta - 1 < r) :
    0 < 1 - momentExponent r beta := by
  rw [momentExponent]
  have hden : (2 * r : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  have hnum : 0 < 2 * r - (beta + r - 1) := by nlinarith
  nlinarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta4_r89_one_sub
#print axioms momentExponent_one_sub_nonneg
#print axioms momentExponent_one_sub_pos

end ProximityGap.MomentExponentThreshold
