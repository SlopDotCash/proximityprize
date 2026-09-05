import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius rate-gap relations

The Reed–Solomon capacity-minus-Johnson gap `√ρ - ρ` is positive on
`(0,1)` and zero at both endpoints. This file proves these implications
and endpoint values; it does not state a converse for unrestricted real rates.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The RS gap `√ρ - ρ` is positive on the open interval:
`0 < √ρ - ρ` for `0 < ρ < 1`. -/
theorem rs_gap_pos {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < Real.sqrt ρ - ρ := by
  have hsq : ρ ^ 2 < ρ := by
    nlinarith [sq_nonneg (ρ : ℝ)]
  have key : ρ < Real.sqrt ρ := Real.lt_sqrt_of_sq_lt hsq
  linarith

/-- The RS gap is zero at the endpoints: `√0 - 0 = 0` and
`√1 - 1 = 0`. -/
theorem rs_gap_endpoints_zero :
    Real.sqrt (0 : ℝ) - 0 = 0 ∧ Real.sqrt (1 : ℝ) - 1 = 0 := by
  constructor <;> norm_num

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms rs_gap_pos
#print axioms rs_gap_endpoints_zero

end ArkLib.JohnsonCapacity
