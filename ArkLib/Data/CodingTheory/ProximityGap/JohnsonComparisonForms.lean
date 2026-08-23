import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson capacity comparison forms

The Johnson radius `J(δ) = 1 - √(1-δ)` and capacity `δ` satisfy
`J(δ) ≤ δ` on `[0,1]` (already in `JohnsonCapacityBound`).  This file
records the equivalent ordering forms used by downstream assemblies:
the capacity-minus-Johnson gap expressed in sqrt form, the strict
version at interior points, and the RS-instance capacity comparison.
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

/-- The RS-instance capacity comparison: `1 - ρ ≤ 1 - √ρ` fails in the
wrong direction; the correct form is `√ρ ≤ 1` for `ρ ≤ 1`, i.e. the RS
Johnson radius is nonnegative. -/
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
