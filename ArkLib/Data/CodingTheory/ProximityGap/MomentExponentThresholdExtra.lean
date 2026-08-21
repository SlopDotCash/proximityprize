import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- The gap to triviality: `1 - θ(r,β) = (r - (β-1)) / (2r)`.
Mirror of `momentExponent_sub_half`; used to state the triviality boundary
in terms of the remaining gap above the unattained `θ = 1` regime. -/
theorem momentExponent_one_sub {r beta : ℝ} (hr : 0 < r) :
    1 - momentExponent r beta = (r - (beta - 1)) / (2 * r) := by
  rw [momentExponent]
  have hden : (2 * r : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- For fixed depth `r`, the exponent is strictly increasing in `β`.
Complement of `momentExponent_strictAnti` (which varies `r`). -/
theorem momentExponent_strictMono {r beta₁ beta₂ : ℝ} (hr : 0 < r)
    (hb : beta₁ < beta₂) :
    momentExponent r beta₁ < momentExponent r beta₂ := by
  rw [momentExponent, momentExponent]
  have hpos : (0 : ℝ) < 2 * r := by positivity
  rw [div_lt_div_iff₀ hpos hpos]
  nlinarith

/-- The triviality boundary in gap form: below the crossover the remaining
gap to `1` is positive; exactly at `r = β-1` the gap is zero. -/
theorem momentExponent_one_sub_eq_zero_iff {r beta : ℝ} (hr : 0 < r) :
    1 - momentExponent r beta = 0 ↔ r = beta - 1 := by
  rw [momentExponent_one_sub hr]
  have hden : (2 * r : ℝ) ≠ 0 := by positivity
  have hz : (r - (beta - 1)) / (2 * r) = 0 ↔ r - (beta - 1) = 0 := by
    constructor
    · intro h
      have hnum : (r - (beta - 1)) = (2 * r) * ((r - (beta - 1)) / (2 * r)) := by
        field_simp [hden]
      rw [h] at hnum
      nlinarith
    · intro h
      rw [h]
      simp
  rw [hz]
  constructor <;> intro h <;> linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_one_sub
#print axioms momentExponent_strictMono
#print axioms momentExponent_one_sub_eq_zero_iff

end ProximityGap.MomentExponentThreshold
