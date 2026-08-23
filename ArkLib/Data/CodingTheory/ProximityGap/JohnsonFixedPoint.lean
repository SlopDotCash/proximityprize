import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius fixed-point and zero properties

The Johnson radius `J(δ) = 1 - √(1-δ)` on `[0,1]`:

* has a unique fixed point at `δ = 0`: `J(0) = 0`, and `J(δ) < δ`
  for `0 < δ` (it never overshoots capacity).
* has `J(1) = 1` at the top endpoint.

This file records the fixed-point/zero facts.

* `johnson_fixed_zero` — `J(0) = 0`.
* `johnson_lt_identity` — `J(δ) < δ` for `0 < δ < 1`.
* `johnson_top` — `J(1) = 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius fixes zero: `J(0) = 1 - √1 = 0`. -/
theorem johnson_fixed_zero : 1 - Real.sqrt (1 - 0) = 0 := by
  norm_num

/-- The Johnson radius is strictly below the identity on `(0,1)`:
`J(δ) < δ`. -/
theorem johnson_lt_identity {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    1 - Real.sqrt (1 - δ) < δ := by
  have hd : (0 : ℝ) < 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 < 1 - δ := by
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  have key : (1 - δ) < Real.sqrt (1 - δ) := Real.lt_sqrt_of_sq_lt hsq
  linarith

/-- The Johnson radius reaches the top: `J(1) = 1 - √0 = 1`. -/
theorem johnson_top : 1 - Real.sqrt (1 - 1) = 1 := by
  norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_fixed_zero
#print axioms johnson_lt_identity
#print axioms johnson_top

end ArkLib.JohnsonCapacity
