import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The prize-floor bound is strict for β > 1.**
`θ(r,β) > 1/2` whenever `1 < β` and `0 < r` — the closed-form
lower bound. Complements `half_lt_momentExponent` (which needs `β ≥ 2`). -/
theorem momentExponent_half_lt_of_one_lt_beta {r beta : ℝ} (hr : 0 < r)
    (hb : 1 < beta) :
    1 / 2 < momentExponent r beta := by
  rw [momentExponent]
  have hden : (0 : ℝ) < 2 * r := by positivity
  have hnum : 0 < beta + r - 1 := by nlinarith
  rw [lt_div_iff₀ hden]
  nlinarith

/-- **The triviality bound is strict for β < r + 1.**
`θ(r,β) < 1` whenever `β < r + 1` — below the crossover the exponent
stays strictly under the trivial ceiling. -/
theorem momentExponent_lt_one_of_beta_lt {r beta : ℝ} (hr : 0 < r)
    (hb : beta < r + 1) :
    momentExponent r beta < 1 := by
  rw [momentExponent]
  have hden : (0 : ℝ) < 2 * r := by positivity
  rw [div_lt_one₀ hden]
  nlinarith

/-- **The production-window sandwich.**
For `1 < β < r + 1` the exponent is strictly between the prize floor and
the trivial ceiling: `1/2 < θ(r,β) < 1`. This is the operating regime
of the δ* campaign in closed form. -/
theorem momentExponent_sandwich {r beta : ℝ} (hr : 0 < r)
    (hb : 1 < beta) (hbt : beta < r + 1) :
    1 / 2 < momentExponent r beta ∧ momentExponent r beta < 1 := by
  constructor
  · exact momentExponent_half_lt_of_one_lt_beta hr hb
  · exact momentExponent_lt_one_of_beta_lt hr hbt

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_half_lt_of_one_lt_beta
#print axioms momentExponent_lt_one_of_beta_lt
#print axioms momentExponent_sandwich

end ProximityGap.MomentExponentThreshold
