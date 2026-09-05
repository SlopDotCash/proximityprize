import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius derivative-free bounds

Elementary bounds for the Johnson radius: `J(δ) ≤ δ` on `[0,1]`,
strict RS capacity comparison on `(0,1)`, and decreasing RS capacity.
No Taylor estimate is proved here.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius is bounded by capacity with the explicit
witness `√(1-δ) ≥ 1 - δ`: `J(δ) ≤ δ` for `δ ∈ [0,1]`. -/
theorem johnson_le_delta_witness {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    1 - Real.sqrt (1 - δ) ≤ δ := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by
    have hle : (1 - δ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  have key : (1 - δ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The RS capacity `1 - ρ` exceeds the RS Johnson radius `1 - √ρ` on
the interior, restated as the strict gap `√ρ - ρ > 0`. -/
theorem rs_capacity_exceeds_johnson {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    1 - Real.sqrt ρ < 1 - ρ := by
  have hsq : ρ ^ 2 < ρ := by
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ < Real.sqrt ρ := Real.lt_sqrt_of_sq_lt hsq
  linarith

/-- The RS capacity `1 - ρ` is a decreasing function of the rate. -/
theorem rs_capacity_anti {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    1 - ρ₂ ≤ 1 - ρ₁ := by
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_le_delta_witness
#print axioms rs_capacity_exceeds_johnson
#print axioms rs_capacity_anti

end ArkLib.JohnsonCapacity
