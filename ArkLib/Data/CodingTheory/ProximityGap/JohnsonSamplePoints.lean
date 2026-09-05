import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius sample points

The Johnson radius at `δ = 1/2` and `δ = 1/4` is recorded in square-root
form. The file also proves its monotonicity for ordered inputs in `[0,1]`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- `J(1/2) = 1 - √(1/2)`.  Recorded without evaluating `√(1/2)`. -/
theorem johnson_half : 1 - Real.sqrt (1 - 1 / 2) = 1 - Real.sqrt (1 / 2 : ℝ) := by
  ring

/-- `J(1/4) = 1 - √(3/4)`.  Recorded in sqrt form. -/
theorem johnson_quarter : 1 - Real.sqrt (1 - 1 / 4) = 1 - Real.sqrt (3 / 4 : ℝ) := by
  ring

/-- The Johnson radius is increasing, in difference form:
`J(δ₁) ≤ J(δ₂)` for `0 ≤ δ₁ ≤ δ₂ ≤ 1`. -/
theorem johnson_mono_diff {δ₁ δ₂ : ℝ} (h0 : 0 ≤ δ₁) (h12 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 1) :
    1 - Real.sqrt (1 - δ₁) ≤ 1 - Real.sqrt (1 - δ₂) := by
  have hd : (0 : ℝ) ≤ 1 - δ₂ := by linarith
  have hle : 1 - δ₂ ≤ 1 - δ₁ := by linarith
  have hs : Real.sqrt (1 - δ₂) ≤ Real.sqrt (1 - δ₁) :=
    Real.sqrt_le_sqrt hle
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_half
#print axioms johnson_quarter
#print axioms johnson_mono_diff

end ArkLib.JohnsonCapacity
