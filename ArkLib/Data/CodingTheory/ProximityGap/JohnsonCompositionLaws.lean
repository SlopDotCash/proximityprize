import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius composition laws

The rate substitution `J(1-ρ) = 1 - √ρ`, the identity
`δ - J(δ) = √(1-δ) + δ - 1`, and nonnegativity of the RS gap on `[0,1]`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- In rate form `ρ = 1 - δ`, the Johnson radius is `J(1-ρ) = 1 - √ρ`. -/
theorem johnson_rs_rate_form {ρ : ℝ} :
    1 - Real.sqrt (1 - (1 - ρ)) = 1 - Real.sqrt ρ := by
  ring_nf

/-- The capacity-minus-Johnson gap in square-root form. -/
theorem johnson_gap_ident {δ : ℝ} :
    δ - (1 - Real.sqrt (1 - δ)) = Real.sqrt (1 - δ) + δ - 1 := by
  ring

/-- The square root dominates the rate on `[0,1]`. -/
theorem rs_sqrt_ge_rate {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ρ ≤ Real.sqrt ρ := by
  have hsq : ρ ^ 2 ≤ ρ := by
    have hle : (ρ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (ρ : ℝ)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The RS gap `√ρ - ρ` is nonnegative on `[0,1]`. -/
theorem rs_gap_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    0 ≤ Real.sqrt ρ - ρ := by
  have hge : ρ ≤ Real.sqrt ρ := rs_sqrt_ge_rate h0 h1
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_rs_rate_form
#print axioms johnson_gap_ident
#print axioms rs_sqrt_ge_rate
#print axioms rs_gap_nonneg

end ArkLib.JohnsonCapacity
