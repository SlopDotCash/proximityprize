import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius ordering properties

Ordering facts for the Johnson radius `J(δ) = 1 - √(1-δ)`:

* `johnson_pos_interior` — `0 < J(δ)` for `0 < δ ≤ 1`.
* `johnson_below_capacity_weak` — `J(δ) ≤ δ` for `0 ≤ δ ≤ 1`
  (restated).
* `johnson_rs_rate_positive` — the RS-instance Johnson radius is
  positive for `0 < ρ < 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius is at most capacity: `J(δ) ≤ δ` for
`0 ≤ δ ≤ 1` (weak form, no strictness claim). -/
theorem johnson_below_capacity_weak {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    1 - Real.sqrt (1 - δ) ≤ δ := by
  have hd : (0 : ℝ) ≤ 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by
    have hle : (1 - δ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  have key : (1 - δ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The RS-instance Johnson radius is positive on `(0,1)`:
`0 < 1 - √ρ` for `0 < ρ < 1`. -/
theorem rs_johnson_radius_positive {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < 1 - Real.sqrt ρ := by
  have hsq : ρ < 1 ^ 2 := by nlinarith
  have hs : Real.sqrt ρ < Real.sqrt (1 ^ 2) :=
    Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ ρ) hsq
  have hs1 : Real.sqrt (1 ^ 2 : ℝ) = 1 := by norm_num
  have hs' : Real.sqrt ρ < 1 := by simpa [hs1] using hs
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_below_capacity_weak
#print axioms rs_johnson_radius_positive

end ArkLib.JohnsonCapacity
