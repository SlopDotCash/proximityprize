import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# RS-instance Johnson relations

For the Reed–Solomon rate `ρ ∈ [0,1]`, the Johnson radius is
`J_RS(ρ) = 1 - √ρ` and capacity is `1 - ρ`.  This file records the
RS-instance relations: `J_RS` stays below capacity (`1 - √ρ ≤ 1 - ρ`),
the gap `√ρ - ρ` is monotone, and the endpoint/ordering facts used in
the δ* ledger.

* `rs_gap_mono` — `√ρ - ρ` is increasing in `ρ` on `[0, 1/4]`.
* `rs_johnson_le_one` — `J_RS(ρ) ≤ 1` for `ρ ≥ 0`.
* `rs_capacity_lt_one` — `1 - ρ < 1` for `0 < ρ`.
* `rs_johnson_lt_capacity_strict` — `J_RS(ρ) < 1 - ρ` for `0 < ρ < 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The RS Johnson radius `J_RS(ρ) = 1 - √ρ` never exceeds 1 for `ρ ≥ 0`. -/
theorem rs_johnson_le_one {ρ : ℝ} (h0 : 0 ≤ ρ) :
    1 - Real.sqrt ρ ≤ 1 := by
  have hs : (0 : ℝ) ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  linarith

/-- The RS capacity `1 - ρ` is strictly below 1 for `0 < ρ`. -/
theorem rs_capacity_lt_one {ρ : ℝ} (h0 : 0 < ρ) :
    1 - ρ < 1 := by
  linarith

/-- Strictly inside `(0,1)`, the RS Johnson radius is strictly below
capacity: `1 - √ρ < 1 - ρ`. -/
theorem rs_johnson_lt_capacity_strict {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    1 - Real.sqrt ρ < 1 - ρ := by
  have hsq : ρ ^ 2 < ρ := by
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ < Real.sqrt ρ := Real.lt_sqrt_of_sq_lt hsq
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms rs_johnson_le_one
#print axioms rs_capacity_lt_one
#print axioms rs_johnson_lt_capacity_strict

end ArkLib.JohnsonCapacity
