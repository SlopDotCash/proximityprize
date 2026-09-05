import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius endpoints

The Johnson radius `J(δ) = 1 - √(1-δ)` satisfies the algebraic
identity `J(δ) + √(1-δ) = 1`, and the RS-instance Johnson radius
`J_RS(ρ) = 1 - √ρ` has clean endpoint values at `ρ = 0` and `ρ = 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- Algebraic identity: `J(δ) + √(1-δ) = 1`. -/
theorem johnson_add_sqrt {δ : ℝ} :
    (1 - Real.sqrt (1 - δ)) + Real.sqrt (1 - δ) = 1 := by
  ring

/-- The RS Johnson radius at `ρ = 0`: `J_RS(0) = 1 - √0 = 1`. -/
theorem rs_johnson_zero : 1 - Real.sqrt (0 : ℝ) = 1 := by
  norm_num

/-- The RS Johnson radius at `ρ = 1`: `J_RS(1) = 1 - √1 = 0`. -/
theorem rs_johnson_one : 1 - Real.sqrt (1 : ℝ) = 0 := by
  norm_num

/-- The RS Johnson radius is nonnegative at both endpoints. -/
theorem rs_johnson_endpoints_nonneg :
    0 ≤ 1 - Real.sqrt (0 : ℝ) ∧ 0 ≤ 1 - Real.sqrt (1 : ℝ) := by
  constructor <;> norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_add_sqrt
#print axioms rs_johnson_zero
#print axioms rs_johnson_one
#print axioms rs_johnson_endpoints_nonneg

end ArkLib.JohnsonCapacity
