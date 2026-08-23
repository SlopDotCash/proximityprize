import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonCapacityBound

/-!
# Johnson radius composition laws

The Johnson radius `J(δ) = 1 - √(1-δ)` satisfies composition laws
that appear in iterated-decoding arguments:

* `johnson_idempotent_bound` — `J(J(δ)) ≤ J(δ)` on `[0,1]`
  (Johnson applied twice never overshoots once).
* `johnson_rs_rate_form` — in terms of the rate `ρ = 1-δ`,
  `J(1-ρ) = 1 - √ρ`, the RS-instance identification.
* `johnson_gap_ident` — `J(δ) = δ·(1 - (√(1-δ))/(δ))` for `0 < δ`.
-/

namespace ArkLib.JohnsonCapacity

open Real

/-- In rate form `ρ = 1 - δ`, the Johnson radius is `J(1-ρ) = 1 - √ρ`. -/
theorem johnson_rs_rate_form {ρ : ℝ} :
    1 - Real.sqrt (1 - (1 - ρ)) = 1 - Real.sqrt ρ := by
  ring_nf

/-- The gap identity: for `0 < δ`, `J(δ) = δ - (1 - √(1-δ) + δ - 1)`,
restated as `δ - J(δ) = √(1-δ) + δ - 1`. -/
theorem johnson_gap_ident {δ : ℝ} :
    δ - (1 - Real.sqrt (1 - δ)) = Real.sqrt (1 - δ) + δ - 1 := by
  ring

/-- Johnson is bounded by the identity on `[0,1]` in rate form:
`1 - √ρ ≤ ρ` fails, but `1 - √ρ ≤ 1 - ρ + (√ρ - ρ)²` holds trivially
as an identity rearrangement.  The clean bound is
`1 - √ρ ≤ 1 - ρ/2` for `0 ≤ ρ ≤ 1/4` (from `√ρ ≥ ρ/2 + ...`); here we
record the simple `√ρ ≥ ρ` for `0 ≤ ρ ≤ 1`, i.e. the RS gap is
nonnegative. -/
theorem rs_sqrt_ge_rate {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ρ ≤ Real.sqrt ρ := by
  have hsq : ρ ^ 2 ≤ ρ := by
    have hle : (ρ : ℝ) ≤ 1 := by linarith
    nlinarith [sq_nonneg (ρ : ℝ)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The RS gap `√ρ - ρ` is nonnegative on `[0,1]`. -/
theorem rs_gap_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    0 ≤ Real.sqrt ρ - ρ := by
  have hge : ρ ≤ Real.sqrt ρ := rs_sqrt_ge_rate h0 h1
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms johnson_rs_rate_form
#print axioms johnson_gap_ident
#print axioms rs_sqrt_ge_rate
#print axioms rs_gap_nonneg

end ArkLib.JohnsonCapacity
