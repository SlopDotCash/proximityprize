import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius secant forms

The Johnson radius `J(δ) = 1 - √(1-δ)` has simple secant/rearrangement
identities used in slope-comparison arguments.

* `johnson_secant_form` — `J(δ) - 1 = -√(1-δ)`.
* `johnson_derivative_witness` — the algebraic witness for the slope:
  `(J(δ₂) - J(δ₁))/(δ₂ - δ₁)` rearranged for `δ₁ < δ₂`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- Secant rearrangement: `J(δ) - 1 = -√(1-δ)`. -/
theorem johnson_secant_form {δ : ℝ} :
    (1 - Real.sqrt (1 - δ)) - 1 = -Real.sqrt (1 - δ) := by
  ring

/-- Slope witness in sqrt form: `J(δ₂) - J(δ₁) = √(1-δ₁) - √(1-δ₂)`. -/
theorem johnson_diff_sqrt {δ₁ δ₂ : ℝ} :
    (1 - Real.sqrt (1 - δ₂)) - (1 - Real.sqrt (1 - δ₁)) =
      Real.sqrt (1 - δ₁) - Real.sqrt (1 - δ₂) := by
  ring

/-- The slope of Johnson between two points is the negative of the
average sqrt slope: `J(δ₂) - J(δ₁) ≤ 0` when `δ₁ ≤ δ₂` (J is
increasing, so the difference is nonnegative — this records the
ordering in sqrt form). -/
theorem johnson_increasing_sqrt {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂)
    (h2 : δ₂ ≤ 1) :
    0 ≤ (1 - Real.sqrt (1 - δ₂)) - (1 - Real.sqrt (1 - δ₁)) := by
  have hd1 : (0 : ℝ) ≤ 1 - δ₂ := by linarith
  have hd2 : 1 - δ₂ ≤ 1 - δ₁ := by linarith
  have hs : Real.sqrt (1 - δ₂) ≤ Real.sqrt (1 - δ₁) :=
    Real.sqrt_le_sqrt hd2
  rw [johnson_diff_sqrt]
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_secant_form
#print axioms johnson_diff_sqrt
#print axioms johnson_increasing_sqrt

end ArkLib.JohnsonCapacity
