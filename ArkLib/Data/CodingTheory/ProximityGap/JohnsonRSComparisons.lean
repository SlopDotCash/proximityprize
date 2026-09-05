import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# RS Johnson radius comparisons

The Reed–Solomon Johnson radius `J_RS(ρ) = 1 - √ρ` and the capacity
`1 - ρ` satisfy elementary comparisons used throughout the rate ledger:

* `rs_johnson_below_capacity` — `1 - √ρ ≤ 1 - ρ` for `ρ ∈ [0,1]`.
* `rs_johnson_pos` — `0 < 1 - √ρ` for `0 < ρ < 1`.
* `rs_capacity_pos` — `0 < 1 - ρ` for `ρ < 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The RS Johnson radius is at most the capacity: `1 - √ρ ≤ 1 - ρ`
for `ρ ∈ [0,1]` (equivalent to `ρ ≤ √ρ`). -/
theorem rs_johnson_below_capacity {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    1 - Real.sqrt ρ ≤ 1 - ρ := by
  have hsq : ρ ^ 2 ≤ ρ := by
    have hle : (ρ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ ≤ Real.sqrt ρ := Real.le_sqrt_of_sq_le hsq
  linarith

/-- The RS Johnson radius is strictly positive inside `(0,1)`. -/
theorem rs_johnson_pos {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < 1 - Real.sqrt ρ := by
  have hsq : ρ < 1 ^ 2 := by nlinarith
  have hs : Real.sqrt ρ < Real.sqrt (1 ^ 2) :=
    Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ ρ) hsq
  have hs1 : Real.sqrt (1 ^ 2 : ℝ) = 1 := by norm_num
  have hs' : Real.sqrt ρ < 1 := by simpa [hs1] using hs
  linarith

/-- The RS capacity is strictly positive for `ρ < 1`. -/
theorem rs_capacity_pos {ρ : ℝ} (h1 : ρ < 1) :
    0 < 1 - ρ := by
  linarith

/-- The RS Johnson radius is strictly below capacity inside `(0,1)`,
as a strict version of `rs_johnson_below_capacity`. -/
theorem rs_johnson_strict_below_capacity {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    1 - Real.sqrt ρ < 1 - ρ := by
  have hsq : ρ ^ 2 < ρ := by
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ < Real.sqrt ρ := Real.lt_sqrt_of_sq_lt hsq
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms rs_johnson_below_capacity
#print axioms rs_johnson_pos
#print axioms rs_capacity_pos
#print axioms rs_johnson_strict_below_capacity

end ArkLib.JohnsonCapacity
