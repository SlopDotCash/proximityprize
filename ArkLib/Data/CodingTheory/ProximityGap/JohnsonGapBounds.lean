import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson gap bounds

The Johnson radius `J(δ) = 1 - √(1-δ)` sits strictly inside
`[0, δ]` for `0 < δ < 1`.  This file records the interior-gap facts
that the δ* threshold lives in: `J(δ) < δ`, the distance
`δ - J(δ) = √(1-δ) + δ - 1` is positive, and the RS-instance gap
`ρ - √ρ` is positive for `0 < ρ < 1`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The Johnson radius is strictly below capacity for interior δ:
`J(δ) < δ` for `0 < δ < 1`. -/
theorem johnson_lt_capacity_interior {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    1 - Real.sqrt (1 - δ) < δ := by
  have hd : (0 : ℝ) < 1 - δ := by linarith
  have hsq : (1 - δ) ^ 2 < 1 - δ := by
    nlinarith [sq_nonneg (1 - δ : ℝ)]
  have key : (1 - δ) < Real.sqrt (1 - δ) := Real.lt_sqrt_of_sq_lt hsq
  linarith

/-- The distance from Johnson to capacity is positive:
`δ - J(δ) = δ - 1 + √(1-δ) > 0` for `0 < δ < 1`. -/
theorem johnson_gap_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 < δ - (1 - Real.sqrt (1 - δ)) := by
  have hlt : 1 - Real.sqrt (1 - δ) < δ := johnson_lt_capacity_interior h0 h1
  linarith

/-- The RS-instance distance is positive: `√ρ - ρ > 0` for `0 < ρ < 1`. -/
theorem rs_johnson_gap_pos {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < Real.sqrt ρ - ρ := by
  have hsq : ρ ^ 2 < ρ := by
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ < Real.sqrt ρ := Real.lt_sqrt_of_sq_lt hsq
  linarith

/-- The Johnson radius lies strictly between 0 and 1 for interior δ:
`0 < J(δ) < 1` for `0 < δ < 1`. -/
theorem johnson_interior {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 < 1 - Real.sqrt (1 - δ) ∧ 1 - Real.sqrt (1 - δ) < 1 := by
  constructor
  · have hpos : (0 : ℝ) < 1 - δ := by linarith
    have hs_lt : Real.sqrt (1 - δ) < 1 := by
      have h1sq : Real.sqrt 1 = 1 := Real.sqrt_one
      have hlt : Real.sqrt (1 - δ) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith : 1 - δ < 1)
      simpa [h1sq] using hlt
    linarith
  · have hpos2 : (0 : ℝ) < 1 - δ := by linarith
    have hs : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.2 hpos2
    linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_lt_capacity_interior
#print axioms johnson_gap_pos
#print axioms rs_johnson_gap_pos
#print axioms johnson_interior

end ArkLib.JohnsonCapacity
