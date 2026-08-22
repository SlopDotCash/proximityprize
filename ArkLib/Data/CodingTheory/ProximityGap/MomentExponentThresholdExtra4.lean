import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The β = 2 boundary anchor.** At the lower edge of the `β ≥ 2` regime
(the hypothesis of `half_lt_momentExponent`), `θ(r,2) = (r+1)/(2r)` — the
exact closed form for the boundary exponent. -/
theorem momentExponent_beta2 {r : ℝ} :
    momentExponent r 2 = (r + 1) / (2 * r) := by
  rw [momentExponent]
  ring

/-- **The gap is strictly increasing in β.**
`θ(r,β) - 1/2 = (β-1)/(2r)` grows linearly in β: a larger aspect exponent
means a larger gap above the prize floor. Complement of
`momentExponent_gap_strictAnti` (which varies `r`). -/
theorem momentExponent_gap_strictMono {r beta₁ beta₂ : ℝ} (hr : 0 < r)
    (hb : beta₁ < beta₂) :
    momentExponent r beta₁ - 1 / 2 < momentExponent r beta₂ - 1 / 2 := by
  rw [momentExponent_sub_half hr, momentExponent_sub_half hr]
  have hpos : (0 : ℝ) < 2 * r := by positivity
  rw [div_lt_div_iff₀ hpos hpos]
  nlinarith

/-- **The β = 2 boundary gap.**
At the edge of the half-trivial regime, `θ(r,2) - 1/2 = 1/(2r)` — the
smallest positive gap attainable while staying at `β ≥ 2`. -/
theorem momentExponent_beta2_gap {r : ℝ} (hr : 0 < r) :
    momentExponent r 2 - 1 / 2 = 1 / (2 * r) := by
  rw [momentExponent_sub_half hr]
  ring

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_beta2
#print axioms momentExponent_gap_strictMono
#print axioms momentExponent_beta2_gap

end ProximityGap.MomentExponentThreshold
