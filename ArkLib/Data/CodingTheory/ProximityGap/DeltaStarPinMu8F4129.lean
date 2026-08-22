/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# PROXIMITY PRIZE WORKBENCH — a novel, closed, fully-proven δ* pin (#389/#371)

A **novel, falsifiable, residual-free** δ* theorem for the proximity-gap MCA threshold,
proven end-to-end with no open math.

> **`deltaStar_pin_mu8_F4129`** — for the explicit smooth-domain Reed–Solomon code
> `evalCode g 8 1` on the 8th roots of unity `μ_8 = ⟨g⟩ ⊆ F_4129^×` (`g = 2386`, order 8),
> at target error `ε* = 18/4129`, the mutual-correlated-agreement threshold is **exactly**
> `δ*(C, ε*) = 5/8 = 1 − 3/2³`, **strictly between Johnson `1−√ρ = 1/2`** (`ρ = 1/4`) **and
> capacity `1−ρ = 3/4`** — a genuine *beyond-Johnson* exact pin.

This is the regime `r² ≤ 2^μ + 1` (`9 ≤ 9`) where the supply bracket closes **unconditionally**:
the optimality (no adversary beats the structured family) is provable because `4129 > 8⁴ = 4096`
carries enough `≡ 1 (mod 8)` supply for the KKH26 counting argument. It is the honest closed
analogue of the open prize (same `δ* = 1−r/2^μ` law, same beyond-Johnson placement), differing
only in needing *explicit* supply (provable here; asymptotically open in the `n=2³²` prize regime).
No residual `Prop`, no `sorry`. Issue #389/#371.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.PrizeWorkbench

/-- `4129` is prime (instance needed for `Field (ZMod 4129)`). -/
instance primeFact_DeltaStarPinMu8F4129_1 : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- `g = 2386` generates `μ_8 ⊆ F_4129^×`: order exactly `8 = 2³`
(`g^(2²) = g⁴ = 4128 = −1 ≠ 1`, `g^(2³) = g⁸ = 1`, so by `orderOf_eq_prime_pow`). -/
theorem orderOf_g8 : orderOf (2386 : ZMod 4129) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ¬ (2386 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
  have h8 : (2386 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
  simpa using orderOf_eq_prime_pow (x := (2386 : ZMod 4129)) h4 h8

/-- **THE NOVEL CLOSED δ* PIN (canonical form).**  `δ* = 1 − 3/2³` for the explicit
beyond-Johnson smooth-domain RS code `evalCode 2386 8 1` on `μ_8 ⊆ F_4129`, at
`ε* = ⌊C(8,3)/3⌋/4129 = 18/4129`.  Fully proven, no residual. -/
theorem deltaStar_pin_mu8_F4129 :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (2386 : ZMod 4129) 8 (3 - 2))
        ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 1 - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  exact KKH26CeilingMarch.kkh26_march_deltaStar_pin_canonical
    (p := 4129) (g := (2386 : ZMod 4129)) (μ := 3) (r := 3) (n := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) orderOf_g8 (by norm_num)

/-- **The δ* value in closed lowest terms: `δ* = 5/8`.** -/
theorem deltaStar_mu8_F4129_eq_five_eighths :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (2386 : ZMod 4129) 8 (3 - 2))
        ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 5 / 8 := by
  rw [deltaStar_pin_mu8_F4129]
  refine tsub_eq_of_eq_add ?_
  norm_num

end ArkLib.ProximityGap.PrizeWorkbench

#print axioms ArkLib.ProximityGap.PrizeWorkbench.deltaStar_mu8_F4129_eq_five_eighths
