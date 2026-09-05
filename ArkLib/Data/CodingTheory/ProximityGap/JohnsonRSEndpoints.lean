import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# RS Johnson radius endpoint identities

Endpoint and ordering identities for the RS-instance Johnson radius
`J_RS(ρ) = 1 - √ρ`:

* `rs_johnson_zero_val` — `J_RS(0) = 1`.
* `rs_johnson_one_val` — `J_RS(1) = 0`.
* `rs_johnson_between` — `0 ≤ J_RS(ρ) ≤ 1` for `ρ ∈ [0,1]`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- The RS Johnson radius at `ρ = 0`: `1 - √0 = 1`. -/
theorem rs_johnson_zero_val : 1 - Real.sqrt (0 : ℝ) = 1 := by
  norm_num

/-- The RS Johnson radius at `ρ = 1`: `1 - √1 = 0`. -/
theorem rs_johnson_one_val : 1 - Real.sqrt (1 : ℝ) = 0 := by
  norm_num

/-- The RS Johnson radius is bounded between 0 and 1 for `ρ ∈ [0,1]`. -/
theorem rs_johnson_between {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    0 ≤ 1 - Real.sqrt ρ ∧ 1 - Real.sqrt ρ ≤ 1 := by
  constructor
  · have hsq : ρ ≤ 1 ^ 2 := by nlinarith
    have hs : Real.sqrt ρ ≤ Real.sqrt (1 ^ 2) := Real.sqrt_le_sqrt hsq
    have hs1 : Real.sqrt (1 ^ 2 : ℝ) = 1 := by norm_num
    have hs' : Real.sqrt ρ ≤ 1 := by simpa [hs1] using hs
    linarith
  · have hs : (0 : ℝ) ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
    linarith

/-- The RS Johnson radius is decreasing on `[0,1]`: `J_RS(ρ₂) ≤ J_RS(ρ₁)`
for `0 ≤ ρ₁ ≤ ρ₂ ≤ 1`. -/
theorem rs_johnson_anti {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (h2 : ρ₂ ≤ 1) :
    1 - Real.sqrt ρ₂ ≤ 1 - Real.sqrt ρ₁ := by
  have hs : Real.sqrt ρ₁ ≤ Real.sqrt ρ₂ := Real.sqrt_le_sqrt h12
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms rs_johnson_zero_val
#print axioms rs_johnson_one_val
#print axioms rs_johnson_between
#print axioms rs_johnson_anti

end ArkLib.JohnsonCapacity
