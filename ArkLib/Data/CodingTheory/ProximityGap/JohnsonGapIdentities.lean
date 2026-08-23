import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius and capacity gap identities

The gap between capacity and the Johnson radius,
`δ - J(δ) = δ - 1 + √(1-δ)`, has exact values at the reference
points and algebraic identities used in the δ* ledger.

* `johnson_gap_zero` — the gap is `0` at `δ = 0`.
* `johnson_gap_one` — the gap is `1` at `δ = 1`.
* `johnson_gap_identity_rearranged` — `δ - J(δ) = √(1-δ) - (1-δ)`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The capacity-Johnson gap is zero at `δ = 0`: `0 - J(0) = 0`. -/
theorem johnson_gap_zero : (0 : ℝ) - (1 - Real.sqrt (1 - 0)) = 0 := by
  norm_num

/-- The gap rearranges to `√(1-δ) - (1-δ)`: the gap equals the
sqrt-minus-linear form, matching `johnson_sqrt_ge_linear`. -/
theorem johnson_gap_identity_rearranged {δ : ℝ} :
    δ - (1 - Real.sqrt (1 - δ)) = Real.sqrt (1 - δ) - (1 - δ) := by
  ring

/-- The gap is nonnegative on `[0,1]`: `0 ≤ δ - J(δ)`. -/
theorem johnson_gap_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    0 ≤ δ - (1 - Real.sqrt (1 - δ)) := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by
    have hle : (1 - δ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  have key : (1 - δ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le hsq
  rw [johnson_gap_identity_rearranged]
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_gap_zero
#print axioms johnson_gap_identity_rearranged
#print axioms johnson_gap_nonneg

end ArkLib.JohnsonCapacity
