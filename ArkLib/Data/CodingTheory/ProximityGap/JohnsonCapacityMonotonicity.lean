import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Monotonicity of the Johnson radius

The Johnson list-decoding radius `J(δ) = 1 - √(1 - δ)` is strictly
increasing in the relative minimum distance `δ ∈ [0,1]`: a larger minimum
distance means a larger Johnson radius.  This file adds the
monotonicity/endpoint lemmas to the existing
`johnson_le_capacity`-family in `JohnsonCapacityBound`.

* `johnson_mono` — `J(δ₁) ≤ J(δ₂)` for `0 ≤ δ₁ ≤ δ₂ ≤ 1`.
* `johnson_strictMono` — strict for `δ₁ < δ₂`.
* `johnson_zero` / `johnson_one` — endpoints `J(0) = 0`, `J(1) = 1`.
* `johnson_rs_anti` — the RS instance `1 - √ρ` is decreasing in `ρ`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius is nondecreasing: for `0 ≤ δ₁ ≤ δ₂ ≤ 1`,
`J(δ₁) = 1 - √(1-δ₁) ≤ 1 - √(1-δ₂) = J(δ₂)`. -/
theorem johnson_mono {δ₁ δ₂ : ℝ} (h0 : 0 ≤ δ₁) (h12 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 1) :
    1 - Real.sqrt (1 - δ₁) ≤ 1 - Real.sqrt (1 - δ₂) := by
  have hd1 : (0 : ℝ) ≤ 1 - δ₂ := by linarith
  have hd2 : 1 - δ₂ ≤ 1 - δ₁ := by linarith
  have hs : Real.sqrt (1 - δ₂) ≤ Real.sqrt (1 - δ₁) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- The Johnson radius is strictly increasing: for `0 ≤ δ₁ < δ₂ < 1`,
`J(δ₁) < J(δ₂)`. -/
theorem johnson_strictMono {δ₁ δ₂ : ℝ} (h0 : 0 ≤ δ₁) (h12 : δ₁ < δ₂) (h2 : δ₂ < 1) :
    1 - Real.sqrt (1 - δ₁) < 1 - Real.sqrt (1 - δ₂) := by
  have hd1 : (0 : ℝ) < 1 - δ₂ := by linarith
  have hd2 : 1 - δ₂ < 1 - δ₁ := by linarith
  have hs : Real.sqrt (1 - δ₂) < Real.sqrt (1 - δ₁) :=
    Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ 1 - δ₂) hd2
  linarith

/-- Endpoint `J(0) = 0`. -/
theorem johnson_zero : 1 - Real.sqrt (1 - 0) = 0 := by
  norm_num

/-- Endpoint `J(1) = 1`. -/
theorem johnson_one : 1 - Real.sqrt (1 - 1) = 1 := by
  norm_num

/-- The Reed–Solomon Johnson radius `1 - √ρ` is decreasing in `ρ ∈ [0,1]`. -/
theorem johnson_rs_anti {ρ₁ ρ₂ : ℝ} (h12 : ρ₁ ≤ ρ₂) :
    1 - Real.sqrt ρ₂ ≤ 1 - Real.sqrt ρ₁ := by
  have hs : Real.sqrt ρ₁ ≤ Real.sqrt ρ₂ := Real.sqrt_le_sqrt h12
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_mono
#print axioms johnson_strictMono
#print axioms johnson_zero
#print axioms johnson_one
#print axioms johnson_rs_anti

end ArkLib.JohnsonCapacity
