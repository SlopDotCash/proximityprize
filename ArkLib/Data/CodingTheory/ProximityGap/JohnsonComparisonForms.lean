import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson capacity comparison forms

Equivalent square-root forms for Johnson bounds: the capacity gap identity,
`1 - δ ≤ √(1-δ)` on `[0,1]`, and the square-root upper bounds that imply
nonnegative Johnson radii.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- Capacity minus Johnson, in closed form:
`δ - J(δ) = δ - 1 + √(1-δ)`. -/
theorem johnson_gap_closed_form {δ : ℝ} :
    δ - (1 - Real.sqrt (1 - δ)) = δ - 1 + Real.sqrt (1 - δ) := by
  ring

/-- The gap `δ - J(δ)` is nonnegative on `[0,1]`, restated as
`√(1-δ) ≥ 1 - δ` (equivalent to `J(δ) ≤ δ`). -/
theorem johnson_sqrt_ge_linear {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    1 - δ ≤ Real.sqrt (1 - δ) := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by
    have hle : (1 - δ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The square root of a rate in `[0,1]` is at most one. -/
theorem rs_sqrt_le_one {ρ : ℝ} (hρ : ρ ≤ 1) (h0 : 0 ≤ ρ) :
    Real.sqrt ρ ≤ 1 := by
  have hsq : ρ ≤ 1 ^ 2 := by nlinarith
  have hle : Real.sqrt ρ ≤ Real.sqrt (1 ^ 2) := Real.sqrt_le_sqrt hsq
  simpa using hle

/-- The Johnson radius is nonnegative on `[0,1]`, restated via
`√(1-δ) ≤ 1`. -/
theorem johnson_nonneg_sqrt_form {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    Real.sqrt (1 - δ) ≤ 1 := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hle : 1 - δ ≤ 1 := by linarith
  calc
    Real.sqrt (1 - δ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
    _ = 1 := Real.sqrt_one

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_gap_closed_form
#print axioms johnson_sqrt_ge_linear
#print axioms rs_sqrt_le_one
#print axioms johnson_nonneg_sqrt_form

end ArkLib.JohnsonCapacity
